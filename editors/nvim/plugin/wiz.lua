if vim.g.loaded_wiz then
  return
end
vim.g.loaded_wiz = true

local cmd = vim.api.nvim_create_user_command

cmd('WizInfoviewToggle', function()
  require('wiz.infoview').toggle()
end, { desc = 'Open or close the Wiz infoview' })
cmd('WizInfoviewOpen', function()
  require('wiz.infoview').open()
end, { desc = 'Open the Wiz infoview' })
cmd('WizInfoviewClose', function()
  require('wiz.infoview').close()
end, { desc = 'Close the Wiz infoview' })
cmd('WizInfoviewRefresh', function()
  require('wiz.infoview').refresh()
end, { desc = 'Ask the server for the state at the cursor again' })

cmd('WizAbbrev', function(o)
  local lines = require('wiz.abbreviations').describe(o.args)
  if #lines > 0 then
    vim.api.nvim_echo({ { table.concat(lines, '\n') } }, false, {})
  end
end, { nargs = '?', desc = 'How to type a symbol (or the one under the cursor), or what an abbreviation types' })

cmd('WizAbbrevList', function()
  local abbr = require 'wiz.abbreviations'
  local lead = require('wiz.config').get().abbreviations.leader
  local rows = {}
  for k, v in pairs(abbr.table()) do
    table.insert(rows, ('%-24s %s'):format(lead .. k, (v:gsub('%$CURSOR', '…'))))
  end
  table.sort(rows)
  vim.cmd 'new'
  vim.api.nvim_buf_set_lines(0, 0, -1, false, rows)
  vim.bo.buftype, vim.bo.bufhidden, vim.bo.modifiable = 'nofile', 'wipe', false
  vim.api.nvim_buf_set_name(0, 'wiz://abbreviations')
end, { desc = 'List every abbreviation in a scratch buffer' })

cmd('WizLspRestart', function()
  require('wiz.lsp').restart()
end, { desc = 'Restart wiz lsp' })
