(*
 * Copyright (C) 2003-2004:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(** {2 Debugger and logger} *)

  (** log level
   * 0    -> logging disabled
   * 1    -> standard logging
   * >=2  -> verbose logging
   * default is 1 *)
val get_log_level: unit -> int
val set_log_level: int -> unit

  (** log a message through the logger with a given log level
   * level defaults to 1, higher level denotes more verbose messages which are
   * ignored with the default log_level *)
val log: ?level: int -> string -> unit

  (** if set to Some fname, fname will be used as a logfile, otherwise stderr
   * will be used *)
val get_log_file: unit -> string option
val set_log_file: string option -> unit
val close_log_file: unit -> unit

