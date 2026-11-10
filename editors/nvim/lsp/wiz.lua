-- For Neovim ≥ 0.11's `vim.lsp.config` / `vim.lsp.enable 'wiz'` (and nvim-lspconfig's
-- `lsp/` configs). If you use this, set `lsp = { enable = false }` in wiz.nvim's setup so
-- the plugin doesn't start a second server.
local lsp = require 'wiz.lsp'
return {
  cmd = { 'wiz', 'lsp' },
  filetypes = { 'wiz' },
  root_markers = { 'grail.wiz', 'wiz-toolchain', 'lakefile.toml', '.git' },
  capabilities = lsp.capabilities(),
  handlers = lsp.handlers,
}
