/*

File: prettify.sig
Author: Alan Smaill / James Brotherston
Description:  Mark up syntax for the pretty printer
Last Modified: 14th August 2002.

*/

sig prettify.

accum_sig lclam_syntax, pretty_print.

type prettify_term     osyn -> thing -> o.
type prettify_special  osyn -> thing -> o.

type pretty_show_term  osyn -> o.
type pretty_show_goal  goal -> o.
type pretty_show_goal_special  goal -> o.

end
