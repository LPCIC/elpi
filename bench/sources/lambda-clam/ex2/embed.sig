/*

File: embed.sig
Author: Louise Dennis / James Brotherston
Description:  Embeddings (as used by rippling)
Last Modified: 20th August 2002

*/

sig embed.

accum_sig logic_eq_constants, pairs.


% tree is embedding of second argument into third argument.

type embeds        etree -> osyn -> osyn -> o.

% An ordering on embeddings.

type check_measure_reducing mkey -> dir -> etree -> etree -> (list int) -> etree -> o.


end















