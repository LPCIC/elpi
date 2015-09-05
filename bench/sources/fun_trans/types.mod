module types.

output_tp Ch T :- printterm Ch T.

print_tp T :- output_tp std_out T.
