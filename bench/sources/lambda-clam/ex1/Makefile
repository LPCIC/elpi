# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../../teyjus

.PHONY: all lclam planner basic_types lclam_syntax plan constructive_logic pretty_printer lclam_utils rewrite_types critics logic_eq_constants ripple_types ex1 sockets goal mathweb syntax interaction method theory_db lclam_list objlists wave_critics lclam_map pairs induction schemes generalise pwf wave embed rewriting print_syntax



all: lclam planner basic_types lclam_syntax plan constructive_logic pretty_printer lclam_utils rewrite_types critics logic_eq_constants ripple_types ex1 sockets goal mathweb syntax interaction method theory_db lclam_list objlists wave_critics lclam_map pairs inductioni schemes generalise pwf wave embed rewriting print_syntax   


run:
	$(TEYJUS)/tjsim -m 1 -b -s 'main.' ex1

arithmetic: arithmetic.lp         
lclam: lclam.lp              
planner: planner.lp
basic_types: basic_types.lp         
lclam_syntax: lclam_syntax.lp       
plan: plan.lp
constructive_logic: constructive_logic.lp         
pretty_printer: pretty_printer.lp
lclam_utils: lclam_utils.lp         
rewrite_types: rewrite_types.lp
critics: critics.lp             
logic_eq_constants: logic_eq_constants.lp  
ripple_types: ripple_types.lp
ex1: ex1.lp                                 
sockets: sockets.lp
goal: goal.lp                
mathweb: mathweb.lp             
syntax: syntax.lp
interaction: interaction.lp         
method: method.lp              
theory_db: theory_db.lp
lclam_list: lclam_list.lp          
objlists: objlists.lp            
wave_critics: wave_critics.lp
lclam_map: lclam_map.lp           
pairs: pairs.lp
induction: induction.lp
schemes: schemes.lp
generalise: generalise.lp
pwf: pwf.lp
wave: wave.lp
embed: embed.lp
rewriting: rewriting.lp
print_syntax: print_syntax.lp

           
# Everything after this point is generic and should be duplicated
# in user's makefiles

%.lpo : %.mod %.sig
	$(TEYJUS)/tjcc $*

%.lp : %.lpo
	$(TEYJUS)/tjlink $*

-include depend
depend: *.mod *.sig
	$(TEYJUS)/tjdepend *.mod > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp depend
