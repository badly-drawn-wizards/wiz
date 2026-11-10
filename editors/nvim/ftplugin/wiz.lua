if vim.b.did_ftplugin then
  return
end
vim.b.did_ftplugin = true

vim.bo.commentstring = '-- %s'
vim.bo.comments = 's0:/-,mb: ,ex:-/,:--'
vim.bo.expandtab = true
vim.bo.shiftwidth = 2
vim.bo.softtabstop = 2
vim.b.undo_ftplugin = 'setlocal commentstring< comments< expandtab< shiftwidth< softtabstop<'

require('wiz').attach(vim.api.nvim_get_current_buf())
