-- wiz.nvim: Wiz in Neovim. `require('wiz').setup { ... }` (optional; see wiz.config for
-- the options). The ftplugin calls `attach` for every wiz buffer.
local config = require 'wiz.config'

local M = {}

function M.setup(opts)
  config.set(opts)
  require('wiz.abbreviations').reload()
  -- buffers opened before setup (lazy loading) get the new settings too
  for _, buf in ipairs(vim.api.nvim_list_bufs()) do
    if vim.api.nvim_buf_is_loaded(buf) and vim.bo[buf].filetype == 'wiz' then
      M.attach(buf)
    end
  end
end

local function buffer_maps(buf)
  local map = function(mode, lhs, rhs, desc)
    vim.keymap.set(mode, lhs, rhs, { buffer = buf, silent = true, desc = 'wiz.nvim: ' .. desc })
  end
  map('n', '<LocalLeader>i', require('wiz.infoview').toggle, 'toggle the infoview')
  map('n', '<LocalLeader>r', require('wiz.infoview').refresh, 'refresh the infoview')
  map('n', '<LocalLeader>\\', '<Cmd>WizAbbrev<CR>', 'how to type the character under the cursor')
end

function M.attach(buf)
  if vim.b[buf].wiz_attached then
    return
  end
  vim.b[buf].wiz_attached = true
  require('wiz.abbreviations').attach(buf)
  require('wiz.infoview').attach(buf)
  if config.get().mappings then
    buffer_maps(buf)
  end
  require('wiz.lsp').start(buf)
end

return M
