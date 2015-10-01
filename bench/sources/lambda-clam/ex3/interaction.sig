/*

File: interaction.sig
Author: Louise Dennis / James Brotherston
Description:  Predicates for controlling the various interaction modes
Last Modified: 14th August 2002.

*/

sig interaction.

kind interaction type.
kind switch      type.
kind meth        type.

type on   switch.
type off  switch.

%% Interaction modes

type interactive_mode interaction -> o.
type interactive      interaction -> o.

type command          interaction.
type command_pretty   interaction.
type xbarnacle        interaction.
type sock_read_write  interaction.
type open_math        interaction.

%% Pretty printing switches

type plan_printing_switch switch -> o.
type plan_printing_sw     switch -> o.

%% Output mode predicates
type verbose         switch -> o.
type silent          switch -> o.
type super_silent    switch -> o.

%% Output mode labels
type verbose_m       switch -> o.
type silent_m        switch -> o.
type super_silent_m  switch -> o.

%% Types for user intervention commands.

type continue o.
type abandon o.
type backtrack o.
type plan_node (list int) -> o.
type try meth -> o.

end