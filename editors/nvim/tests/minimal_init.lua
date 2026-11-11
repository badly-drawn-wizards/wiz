-- nvim --headless --clean -u tests/minimal_init.lua -l tests/run.lua
-- Environment: WIZ = the wiz executable (default `wiz` on PATH), GRAIL = the grail
-- executable (default `grail`), WIZ_LIB = the standard
-- library (default ../../lib, this checkout's).
local here = vim.fn.fnamemodify(debug.getinfo(1, 'S').source:sub(2), ':p:h')
local plugin = vim.fn.fnamemodify(here, ':h')
vim.opt.runtimepath:prepend(plugin)
vim.opt.swapfile = false
vim.opt.shadafile = 'NONE'
vim.cmd 'filetype plugin on'
vim.cmd 'syntax on'

local wiz = os.getenv 'WIZ' or 'wiz'
local grail = os.getenv 'GRAIL' or 'grail'
local lib = os.getenv 'WIZ_LIB' or vim.fn.fnamemodify(plugin .. '/../../lib', ':p')
vim.g.wiz_config = {
  lsp = { cmd = { wiz, '-I', lib, 'lsp' }, grail = { cmd = { grail, 'lsp' } } },
  infoview = { debounce = 10 },
}
vim.cmd('runtime! plugin/wiz.lua')
