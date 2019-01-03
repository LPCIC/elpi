/*
 * Some special control predicates of general utility
 */

sig control.

exportdef announce    o -> o.                % for displaying goals
exportdef spi         o -> o.                % display entry and exit from goal
exportdef if          o -> o -> o -> o.      % if then else
exportdef once        o -> o.                % once only predicate
