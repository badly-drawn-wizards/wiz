-- Unicode input: `\lam` → λ, `\r` → →, as in Lean's editors.
--
-- Typing the leader starts an abbreviation (underlined). It is replaced as soon as the
-- next character could not continue any abbreviation (a space, most punctuation, a
-- second leader), when a complete abbreviation can't be extended (`\lambda`), on <Tab>
-- (which is then swallowed), on <CR>, and when leaving insert mode. `\\` types a
-- backslash. The table is Lean's (data/lean-abbreviations.json, from vscode-lean4,
-- Apache-2.0) plus Wiz's additions (wiz.abbreviations_extra) and the user's
-- `abbreviations.extra`.
local config = require 'wiz.config'

local M = {}

local ns = vim.api.nvim_create_namespace 'wiz.abbreviations'

local plugin_root = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':h:h:h')

local table_cache = nil -- { map = {abbrev → symbol}, prefixes = {prefix → true} }

local function read_json(path)
  local f = io.open(path, 'r')
  if not f then
    error(('wiz.nvim: cannot read %s'):format(path))
  end
  local s = f:read '*a'
  f:close()
  return vim.json.decode(s)
end

--- All abbreviations (without the leader) → their expansions.
function M.table()
  if table_cache then
    return table_cache.map
  end
  local map = read_json(plugin_root .. '/data/lean-abbreviations.json')
  for k, v in pairs(require 'wiz.abbreviations_extra') do
    map[k] = v
  end
  for k, v in pairs(config.get().abbreviations.extra or {}) do
    map[k] = v
  end
  local prefixes = {}
  for k in pairs(map) do
    for i = 1, #k do
      prefixes[k:sub(1, i)] = true
    end
  end
  table_cache = { map = map, prefixes = prefixes }
  return map
end

--- Forget the table (after changing `abbreviations.extra`).
function M.reload()
  table_cache = nil
end

local function prefixes()
  M.table()
  return table_cache.prefixes
end

local function leader()
  return config.get().abbreviations.leader
end

--- Expand typed text (starting with the leader): the longest abbreviation that is a
--- prefix of what was typed, then the rest again. Unknown text stays as typed.
--- Returns the expansion and the byte offset of `$CURSOR` in it (or nil).
function M.expand(text)
  local lead = leader()
  local map = M.table()
  local out = {}
  local i = 1
  while i <= #text do
    if text:sub(i, i + #lead - 1) == lead then
      local rest = text:sub(i + #lead)
      if rest:sub(1, #lead) == lead then
        table.insert(out, lead)
        i = i + 2 * #lead
      else
        local best = nil
        for len = #rest, 1, -1 do
          if map[rest:sub(1, len)] then
            best = len
            break
          end
        end
        if best then
          table.insert(out, map[rest:sub(1, best)])
          i = i + #lead + best
        else
          table.insert(out, lead)
          i = i + #lead
        end
      end
    else
      local j = text:find(lead, i, true) or (#text + 1)
      table.insert(out, text:sub(i, j - 1))
      i = j
    end
  end
  local s = table.concat(out)
  local cur = s:find('$CURSOR', 1, true)
  if cur then
    s = s:sub(1, cur - 1) .. s:sub(cur + #'$CURSOR')
    return s, cur - 1
  end
  return s, nil
end

--- The abbreviations that produce `symbol` (with the leader), shortest first.
function M.lookup(symbol)
  local lead = leader()
  local found = {}
  for k, v in pairs(M.table()) do
    if v == symbol or v:gsub('%$CURSOR', '') == symbol then
      table.insert(found, lead .. k)
    end
  end
  table.sort(found, function(a, b)
    return #a < #b or (#a == #b and a < b)
  end)
  return found
end

-- The abbreviation being typed: one per buffer.
-- state[buf] = { mark = extmark id at the leader, maps = saved insert maps }
local state = {}

local function mark_pos(buf, id)
  local p = vim.api.nvim_buf_get_extmark_by_id(buf, ns, id, { details = true })
  if not p or not p[1] then
    return nil
  end
  return p[1], p[2], p[3] and p[3].end_row, p[3] and p[3].end_col
end

-- The text typed since the leader (the extmark grows as it is typed), if it is still
-- on one line and starts with the leader. With `at_cursor`, only if the cursor is at
-- its end (the user is still typing it).
local function pending_text(buf, at_cursor)
  local st = state[buf]
  if not st then
    return nil
  end
  local row, col, erow, ecol = mark_pos(buf, st.mark)
  if not row or erow ~= row or ecol <= col then
    return nil
  end
  if at_cursor then
    local win = vim.api.nvim_get_current_win()
    if vim.api.nvim_win_get_buf(win) ~= buf then
      return nil
    end
    local cur = vim.api.nvim_win_get_cursor(win)
    if cur[1] - 1 ~= row or cur[2] ~= ecol then
      return nil
    end
  end
  local line = vim.api.nvim_buf_get_lines(buf, row, row + 1, true)[1]
  local text = line:sub(col + 1, ecol)
  if text:sub(1, #leader()) ~= leader() then
    return nil
  end
  return text, row, col
end

local temp_maps = {
  ['<Tab>'] = function()
    return '<Cmd>lua require("wiz.abbreviations").convert()<CR>'
  end,
  ['<CR>'] = function()
    return '<Cmd>lua require("wiz.abbreviations").convert()<CR><CR>'
  end,
}

local function stop(buf)
  local st = state[buf]
  if not st then
    return
  end
  state[buf] = nil
  pcall(vim.api.nvim_buf_del_extmark, buf, ns, st.mark)
  for lhs, saved in pairs(st.maps or {}) do
    pcall(vim.keymap.del, 'i', lhs, { buffer = buf })
    if saved and not vim.tbl_isempty(saved) then
      pcall(vim.fn.mapset, 'i', false, saved)
    end
  end
end

local function start(buf, row, col)
  stop(buf)
  local mark = vim.api.nvim_buf_set_extmark(buf, ns, row, col, {
    end_row = row,
    end_col = col,
    right_gravity = false,
    end_right_gravity = true,
    hl_group = 'WizAbbreviationMark',
  })
  local maps = {}
  for lhs, rhs in pairs(temp_maps) do
    local saved = vim.fn.maparg(lhs, 'i', false, true)
    maps[lhs] = (saved.buffer == 1) and saved or false
    vim.keymap.set('i', lhs, rhs, { buffer = buf, expr = true, desc = 'wiz.nvim: expand the abbreviation' })
  end
  state[buf] = { mark = mark, maps = maps }
end

-- Replace `text`, typed at (row, col) and tracked by the extmark `mark`, with its
-- expansion, keeping the cursor where it is relative to the text after it.
local function replace(buf, mark, text)
  local row, col = mark_pos(buf, mark)
  pcall(vim.api.nvim_buf_del_extmark, buf, ns, mark)
  if not row then
    return
  end
  local line = vim.api.nvim_buf_get_lines(buf, row, row + 1, true)[1]
  if line:sub(col + 1, col + #text) ~= text then
    return
  end
  local new, cursor_at = M.expand(text)
  if new == text then
    return
  end
  local win = vim.api.nvim_get_current_win()
  local here = vim.api.nvim_win_get_buf(win) == buf
  -- the cursor before the edit (set_text moves it, but not always where we want)
  local cur = here and vim.api.nvim_win_get_cursor(win)
  vim.api.nvim_buf_set_text(buf, row, col, row, col + #text, { new })
  if not here then
    return
  end
  if cursor_at then
    vim.api.nvim_win_set_cursor(win, { row + 1, col + cursor_at })
  elseif cur[1] - 1 == row and cur[2] >= col + #text then
    vim.api.nvim_win_set_cursor(win, { row + 1, cur[2] + #new - #text })
  elseif cur[1] - 1 == row and cur[2] > col then
    vim.api.nvim_win_set_cursor(win, { row + 1, col + #new })
  end
end

-- Replace later (we may be inside InsertCharPre, where the text is locked).
local function replace_later(buf, text)
  local st = state[buf]
  local row, col = mark_pos(buf, st.mark)
  local mark = vim.api.nvim_buf_set_extmark(buf, ns, row, col, { right_gravity = false })
  vim.schedule(function()
    if vim.api.nvim_buf_is_valid(buf) then
      replace(buf, mark, text)
    end
  end)
end

--- Expand the abbreviation being typed now (Tab, CR, InsertLeave, :WizAbbrevExpand).
function M.convert()
  local buf = vim.api.nvim_get_current_buf()
  local st = state[buf]
  if not st then
    return
  end
  local text = pending_text(buf, false)
  local mark = st.mark
  local row, col = mark_pos(buf, mark)
  local copy = row and vim.api.nvim_buf_set_extmark(buf, ns, row, col, { right_gravity = false })
  stop(buf)
  if text and copy then
    replace(buf, copy, text)
  elseif copy then
    pcall(vim.api.nvim_buf_del_extmark, buf, ns, copy)
  end
end

-- Is `typed` (text after a leader) complete, with no longer abbreviation?
local function complete(typed)
  local map = M.table()
  if not map[typed] then
    return false
  end
  for k in pairs(map) do
    if #k > #typed and k:sub(1, #typed) == typed then
      return false
    end
  end
  return true
end

local function on_char(buf)
  local char = vim.v.char
  local lead = leader()
  if state[buf] then
    local text = pending_text(buf, true)
    if not text then
      stop(buf)
    else
      -- the abbreviation being typed: the text after the last leader (`\r\x` is two)
      local last = text:match('.*()' .. vim.pesc(lead))
      local segment = text:sub(last + #lead)
      if char == lead then
        if segment == '' then
          -- `\\`: a backslash
          vim.v.char = ''
          if text ~= lead then
            replace_later(buf, text)
          end
          stop(buf)
        end
        -- otherwise a new abbreviation right after this one: keep going
        return
      end
      local typed = segment .. char
      if prefixes()[typed] then
        if complete(typed) then
          replace_later(buf, text .. char)
          stop(buf)
        end
        return
      end
      replace_later(buf, text)
      stop(buf)
    end
  end
  if char == lead then
    local cur = vim.api.nvim_win_get_cursor(0)
    start(buf, cur[1] - 1, cur[2])
  end
end

--- Turn abbreviations on in a buffer.
function M.attach(buf)
  if not config.get().abbreviations.enable then
    return
  end
  vim.api.nvim_set_hl(0, 'WizAbbreviationMark', { default = true, underline = true })
  local group = vim.api.nvim_create_augroup('wiz.abbreviations.' .. buf, { clear = true })
  vim.api.nvim_create_autocmd('InsertCharPre', {
    group = group,
    buffer = buf,
    callback = function()
      on_char(buf)
    end,
  })
  vim.api.nvim_create_autocmd({ 'InsertLeave', 'BufLeave' }, {
    group = group,
    buffer = buf,
    callback = function()
      if state[buf] and vim.api.nvim_get_current_buf() == buf then
        M.convert()
      end
      stop(buf)
    end,
  })
end

--- Is an abbreviation being typed in `buf`? (for statuslines and tests)
function M.active(buf)
  return state[buf or vim.api.nvim_get_current_buf()] ~= nil
end

--- `:WizAbbrev [x]`: with an abbreviation (`lam`, `\lam`), what it types; with a symbol
--- (`λ`), how to type it; with nothing, how to type the character under the cursor.
function M.describe(arg)
  local lead = leader()
  local lines = {}
  if not arg or arg == '' then
    local line = vim.api.nvim_get_current_line()
    local col = vim.api.nvim_win_get_cursor(0)[2]
    local idx = vim.str_utf_start(line, col + 1)
    local start_byte = col + 1 + idx
    local len = vim.str_utf_end(line, start_byte) + 1
    arg = line:sub(start_byte, start_byte + len - 1)
    if arg == '' then
      vim.notify('wiz.nvim: no character under the cursor', vim.log.levels.WARN)
      return {}
    end
  end
  local key = arg:sub(1, #lead) == lead and arg:sub(#lead + 1) or arg
  local map = M.table()
  if map[key] then
    table.insert(lines, ('%s%s → %s'):format(lead, key, (map[key]:gsub('%$CURSOR', ''))))
  end
  local ways = M.lookup(arg)
  if #ways > 0 then
    table.insert(lines, ('Type %s with: %s'):format(arg, table.concat(ways, '  ')))
  end
  if #lines == 0 then
    table.insert(lines, ('No abbreviation for %q (add one with abbreviations.extra)'):format(arg))
  end
  return lines
end

return M
