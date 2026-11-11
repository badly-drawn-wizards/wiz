-- Starting `wiz lsp` and talking to it.
local config = require 'wiz.config'

local M = {}

local function on_elaborated(_, result, ctx)
  require('wiz.infoview').on_elaborated(result, ctx)
end

M.handlers = { ['wiz/elaborated'] = on_elaborated }

--- The client capabilities wiz.nvim asks for: the defaults, plus the
--- `wiz/elaborated` notification (the infoview refreshes on it).
function M.capabilities(extra)
  local caps = vim.lsp.protocol.make_client_capabilities()
  caps.experimental = vim.tbl_extend('force', caps.experimental or {}, { wizElaborated = true })
  return vim.tbl_deep_extend('force', caps, extra or {})
end

--- The project root of `buf`: the nearest directory with a root marker, else the
--- file's own directory.
function M.root(buf)
  local markers = config.get().lsp.root_markers
  local root = vim.fs.root(buf, markers)
  if root then
    return root
  end
  local name = vim.api.nvim_buf_get_name(buf)
  return name ~= '' and vim.fs.dirname(name) or vim.uv.cwd()
end

--- The server command for a project root: `grail lsp -C ROOT` when the root is a grail
--- package (has a grail.wiz) and `lsp.grail.enable` is on, else `lsp.cmd`. If grail is
--- not executable, warns once and falls back to `lsp.cmd`.
function M.cmd(root)
  local cfg = config.get().lsp
  local g = cfg.grail or {}
  if g.enable ~= false and root and vim.uv.fs_stat(root .. '/grail.wiz') then
    local cmd = vim.deepcopy(g.cmd or { 'grail', 'lsp' })
    if vim.fn.executable(cmd[1]) == 1 then
      table.insert(cmd, '-C')
      table.insert(cmd, root)
      return cmd
    end
    vim.notify_once(('wiz.nvim: %s has a grail.wiz but %s is not on PATH; starting %s without the package\'s modules')
      :format(root, cmd[1], cfg.cmd[1]), vim.log.levels.WARN)
  end
  return cfg.cmd
end

--- A `vim.lsp.start` config for `buf`.
function M.client_config(buf)
  local cfg = config.get().lsp
  local root = M.root(buf)
  return {
    name = 'wiz',
    cmd = M.cmd(root),
    root_dir = root,
    capabilities = M.capabilities(cfg.capabilities),
    handlers = M.handlers,
    on_attach = cfg.on_attach,
  }
end

function M.start(buf)
  if not config.get().lsp.enable then
    return
  end
  local cc = M.client_config(buf)
  if vim.fn.executable(cc.cmd[1]) ~= 1 then
    vim.notify_once(('wiz.nvim: %s is not on PATH; no language server'):format(cc.cmd[1]), vim.log.levels.WARN)
    return
  end
  return vim.lsp.start(cc, { bufnr = buf })
end

--- The wiz client attached to `buf`, if any.
function M.client(buf)
  return vim.lsp.get_clients({ bufnr = buf, name = 'wiz' })[1]
end

--- Send `method` with `params` to the wiz client of `buf`; `handler(err, result)`.
function M.request(buf, method, params, handler)
  local client = M.client(buf)
  if not client then
    handler({ code = -1, message = 'no wiz language server for this buffer' }, nil)
    return
  end
  local cb = function(err, result)
    handler(err, result)
  end
  if vim.fn.has 'nvim-0.11' == 1 then
    client:request(method, params, cb, buf)
  else
    client.request(method, params, cb, buf)
  end
end

--- Position params for `win` (its cursor) in the client's encoding.
function M.position_params(win, buf)
  local client = M.client(buf)
  local enc = client and client.offset_encoding or 'utf-16'
  return vim.lsp.util.make_position_params(win, enc)
end

function M.restart()
  for _, client in ipairs(vim.lsp.get_clients { name = 'wiz' }) do
    client:stop()
  end
  vim.defer_fn(function()
    for _, buf in ipairs(vim.api.nvim_list_bufs()) do
      if vim.api.nvim_buf_is_loaded(buf) and vim.bo[buf].filetype == 'wiz' then
        M.start(buf)
      end
    end
  end, 500)
end

return M
