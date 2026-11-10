-- The wiz.nvim tests: abbreviation expansion (typed through real insert mode), and the
-- infoview against the real `wiz lsp` on tests/fixture/Goals.wiz.
-- Run with tests/run.sh (or: nvim --headless --clean -u tests/minimal_init.lua -l tests/run.lua).
local here = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':p:h')
local fixture = here .. '/fixture/Goals.wiz'

local failures, passed = 0, 0
local function test(name, fn)
  io.stdout:write('  … ' .. name .. '\r'); io.stdout:flush()
  local ok, err = pcall(fn)
  if ok then
    passed = passed + 1
    io.stdout:write('  ✓ ' .. name .. '\n')
  else
    failures = failures + 1
    io.stdout:write('  ✗ ' .. name .. '\n      ' .. tostring(err):gsub('\n', '\n      ') .. '\n')
  end
end

local function eq(want, got, what)
  if not vim.deep_equal(want, got) then
    error(('%s: expected %s, got %s'):format(what or 'value', vim.inspect(want), vim.inspect(got)), 2)
  end
end

local function wait(ms, cond, what)
  if not vim.wait(ms, cond, 20) then
    error('timed out waiting for ' .. what, 2)
  end
end

-- Type `keys` in insert mode in a fresh wiz buffer (as typeahead: the expansions
-- scheduled while typing run when nvim next waits), then <Esc>; return the text.
local function typed(keys)
  vim.cmd 'enew!'
  vim.bo.filetype = 'wiz'
  local k = vim.api.nvim_replace_termcodes('i' .. keys .. '<Esc>', true, false, true)
  vim.api.nvim_feedkeys(k, 'tx', false)
  vim.wait(20)
  local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
  vim.bo.modified = false
  return table.concat(lines, '\n')
end

io.stdout:write 'abbreviations\n'

test('the table: Lean\'s, plus Wiz\'s free letters and symbols', function()
  local t = require('wiz.abbreviations').table()
  local want = {
    lam = 'λ', r = '→', to = '→', forall = '∀', all = '∀', ex = '∃', Sigma = 'Σ', x = '×',
    ['=='] = '≡', le = '≤', ne = '≠', a = 'α', b = 'β', z = 'ζ', f = 'φ', ['0'] = '₀',
    ['1'] = '₁', ['<'] = '⟨', ['>'] = '⟩', ['-1'] = '⁻¹', ['|-'] = '⊢', ['++'] = '⧺', l = '←',
  }
  for k, v in pairs(want) do
    eq(v, t[k], '\\' .. k)
  end
end)

test('expand: longest prefix, then the rest', function()
  local e = require('wiz.abbreviations').expand
  eq('λ', (e '\\lam'))
  eq('λb', (e '\\lamb'))
  eq('\\', (e '\\'))
  eq('→×', (e '\\r\\x'))
end)

test('typing: a space ends an abbreviation and stays', function()
  eq('λ x', typed '\\lam x')
  eq('A → B', typed 'A \\r B')
  eq('∀ n, n ≤ n', typed '\\forall n, n \\le n')
end)

test('typing: punctuation that continues no abbreviation ends it', function()
  eq('α)', typed '\\a)')
  eq('Σ(', typed '\\Sigma(')
  eq('x₀,', typed 'x\\0,')
end)

test('typing: abbreviations that are punctuation themselves', function()
  eq('⟨a, b⟩ ', typed '\\<a, b\\> ')
  eq('a ≡ b', typed 'a \\== b')
  eq('f⁻¹ ', typed 'f\\-1 ')
  eq('a ≠ b', typed 'a \\ne b')
end)

test('typing: a second leader ends the first; \\\\ is a backslash', function()
  eq('→× ', typed '\\r\\x ')
  eq('\\lam', typed '\\\\lam')
end)

test('typing: a complete abbreviation that can\'t be extended expands at once', function()
  eq('λ', typed '\\lambda')
  eq('Σ', typed '\\Sigma')
end)

test('typing: Tab expands (and is swallowed); leaving insert mode expands', function()
  eq('ℕ', typed '\\N<Tab>')
  eq('γ', typed '\\g')
  eq('  x', typed '<Tab>x') -- no abbreviation: an ordinary Tab (expandtab)
end)

test('typing one key at a time (an embedded nvim): expansions run between keys', function()
  local init = here .. '/minimal_init.lua'
  local chan = vim.fn.jobstart({ vim.v.progpath, '--embed', '--headless', '--clean', '-u', init }, { rpc = true })
  local function req(...)
    return vim.rpcrequest(chan, ...)
  end
  req('nvim_command', 'enew | setfiletype wiz')
  local keys = { 'i', 'f', ' ', '\\', 'l', 'a', 'm', ' ', 'x', ' ', '\\', 'r', '\\', 'x', ' ', 'y', '\\', '<lt>', 'a', '\\', '>' }
  for _, k in ipairs(keys) do
    req('nvim_input', k)
    vim.wait(30)
    req('nvim_eval', '1') -- let the child finish this key and its scheduled work
  end
  vim.wait(30)
  req('nvim_eval', '1')
  local line = req('nvim_get_current_line')
  local col = req('nvim_win_get_cursor', 0)[2]
  req('nvim_input', '<Esc>')
  vim.fn.jobstop(chan)
  eq('f λ x →× y⟨a\\>', line, 'the line')
  eq(#line, col, 'the cursor at the end')
end)

test('typing: unknown text stays as typed after the longest abbreviation', function()
  eq('\\ x', typed '\\ x')
  eq('θqq ', typed '\\qqq ')
  eq('→\\', typed '\\r\\\\')
end)

test('lookup: :WizAbbrev', function()
  local d = require('wiz.abbreviations').describe
  eq(true, (d('λ')[1] or ''):find('\\lam', 1, true) ~= nil, 'λ lists \\lam')
  eq('\\lam → λ', d('lam')[1])
  eq('\\++ → ⧺', d('\\++')[1])
end)

test('every non-ASCII symbol in lib/*.wiz has an abbreviation', function()
  local lib = os.getenv 'WIZ_LIB' or vim.fn.fnamemodify(here .. '/../../../lib', ':p')
  local symbols = {}
  for _, f in ipairs(vim.fn.globpath(lib, '**/*.wiz', false, true)) do
    for _, line in ipairs(vim.fn.readfile(f)) do
      for ch in line:gmatch '[\xC2-\xF4][\x80-\xBF]*' do
        symbols[ch] = true
      end
    end
  end
  local have = {}
  for _, v in pairs(require('wiz.abbreviations').table()) do
    have[(v:gsub('%$CURSOR', ''))] = true
  end
  local missing = {}
  for ch in pairs(symbols) do
    -- box drawing in comments and combining marks are typed with the letter before them
    if not have[ch] then
      table.insert(missing, ch)
    end
  end
  table.sort(missing)
  eq({}, missing, 'symbols without an abbreviation')
end)

io.stdout:write 'infoview (wiz lsp)\n'

local wiz = vim.g.wiz_config.lsp.cmd[1]
if vim.fn.executable(wiz) ~= 1 then
  io.stdout:write('  (skipped: ' .. wiz .. ' is not executable)\n')
else
  local iv = require 'wiz.infoview'
  local function at(line, col)
    vim.api.nvim_win_set_cursor(0, { line, col })
    vim.api.nvim_exec_autocmds('CursorMoved', { buffer = 0 })
    iv.update_now()
    wait(20000, function()
      return iv.idle() and iv.state.src and iv.state.src.position.line == line - 1
        and iv.state.src.position.character == col
    end, 'the infoview')
    return iv.lines()
  end
  local function has(lines, s)
    for _, l in ipairs(lines) do
      if l == s then
        return true
      end
    end
    error(('no line %q in the infoview:\n%s'):format(s, table.concat(lines, '\n')), 2)
  end

  test('the server starts on a wiz file and the infoview opens', function()
    vim.cmd('edit ' .. vim.fn.fnameescape(fixture))
    eq('wiz', vim.bo.filetype, 'filetype')
    wait(20000, function()
      return require('wiz.lsp').client(0) ~= nil
    end, 'the wiz client')
    wait(5000, iv.is_open, 'the infoview window')
    eq(vim.fs.root(fixture, { 'grail.wiz', 'lakefile.toml', '.git' }), require('wiz.lsp').client(0).config.root_dir, 'root dir')
  end)

  test('the tactic state after `intro n`', function()
    local lines = at(4, 8) -- the end of "  intro n"
    has(lines, 'Tactic state')
    has(lines, 'n : Nat')
    has(lines, '⊢ Bool → Nat')
  end)

  test('the expected type of an argument', function()
    local lines = at(8, 25) -- the first `1` of `Nat.add 1 1`
    has(lines, 'Expected type')
    has(lines, '⊢ Nat')
  end)

  test('tagged text is highlighted by kind, and K inspects the subterm', function()
    local lines = at(4, 8)
    local row = nil
    for i, l in ipairs(lines) do
      if l == '⊢ Bool → Nat' then
        row = i
      end
    end
    local marks = vim.api.nvim_buf_get_extmarks(iv.state.buf, -1, { row - 1, 0 }, { row - 1, -1 }, { details = true })
    local groups = {}
    for _, m in ipairs(marks) do
      groups[m[4].hl_group] = true
    end
    eq(true, groups.WizInfoviewConst, 'Bool and Nat highlighted as constants')
    local col = lines[row]:find('Bool', 1, true) - 1
    local tag = iv.tag_at(row - 1, col)
    eq('const', tag and tag.kind, 'the tag under Bool')
    eq('Bool', tag.name, 'its name')
    -- K in the infoview window
    local src_win = vim.api.nvim_get_current_win()
    vim.api.nvim_set_current_win(iv.win())
    vim.api.nvim_win_set_cursor(0, { row, col })
    iv.state.subterm = nil
    vim.api.nvim_feedkeys('K', 'x', false)
    wait(10000, function()
      return iv.state.subterm ~= nil
    end, 'wiz/subtermInfo')
    eq('Bool', iv.state.subterm.text, 'subterm text')
    eq('Type', iv.flatten(iv.state.subterm.type), 'subterm type')
    vim.api.nvim_set_current_win(src_win)
  end)

  test('the infoview follows edits', function()
    vim.api.nvim_buf_set_lines(0, 2, 3, false, { 'def k : Nat → Nat → Nat := by' })
    vim.api.nvim_win_set_cursor(0, { 4, 8 })
    iv.state.src = nil
    wait(20000, function()
      iv.update_now()
      vim.wait(200, iv.idle)
      return vim.tbl_contains(iv.lines(), '⊢ Nat → Nat')
    end, 'the new goal')
  end)

  test('toggle closes and reopens the window', function()
    vim.cmd 'WizInfoviewToggle'
    eq(false, iv.is_open(), 'closed')
    vim.cmd 'WizInfoviewToggle'
    eq(true, iv.is_open(), 'open')
  end)
end

io.stdout:write(('%d passed, %d failed\n'):format(passed, failures))
vim.cmd((failures == 0) and 'qall!' or 'cquit! 1')
