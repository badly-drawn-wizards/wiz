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

--- A `vim.lsp.start` config for `buf`.
function M.client_config(buf)
  local cfg = config.get().lsp
  return {
    name = 'wiz',
    cmd = cfg.cmd,
    root_dir = M.root(buf),
    capabilities = M.capabilities(cfg.capabilities),
    handlers = M.handlers,
    on_attach = cfg.on_attach,
  }
end

function M.start(buf)
  if not config.get().lsp.enable then
    return
  end
  local cmd = config.get().lsp.cmd
  if vim.fn.executable(cmd[1]) ~= 1 then
    vim.notify_once(('wiz.nvim: %s is not on PATH; no language server'):format(cmd[1]), vim.log.levels.WARN)
    return
  end
  return vim.lsp.start(M.client_config(buf), { bufnr = buf })
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
