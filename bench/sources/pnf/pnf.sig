/* 
 * Interface for code for transforming formulas into prenex normal form
 */

sig pnf.

kind term       type.
kind form       type.
kind i          type. 

type perp       form.
type tru        form.
type and        form -> form -> form.
type or         form -> form -> form.
type imp        form -> form -> form.
type all        (term -> form) -> form.
type some       (term -> form) -> form.
type quant_free form -> o.
type prenex     form -> form -> o.
type merge      form -> form -> o.
type termp      term -> o.
type atom       form -> o.
type a          term.
type b          term.
type c          term.
type f          term -> term.
type formula    i -> form -> o.
type test       i -> form -> o.
type path       term -> term -> form.
type adj        term -> term -> form.
type one        i.
type two        i.
type three      i.
type four       i.
type main       o.
