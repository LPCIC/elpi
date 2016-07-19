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

(* $Id: threadSafe.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

class threadSafe =
  object (self)

    val mutex = Mutex.create ()

      (** condition variable: 'no readers is currently reading' *)
    val noReaders = Condition.create ()

      (** readers count *)
    val mutable readersCount = 0

    method private incrReadersCount = (* internal, not exported *)
      self#doCritical (lazy (
        readersCount <- readersCount + 1
      ))

    method private decrReadersCount = (* internal, not exported *)
      self#doCritical (lazy (
        if readersCount > 0 then readersCount <- readersCount - 1;
      ))

    method private signalNoReaders =  (* internal, not exported *)
      self#doCritical (lazy (
        if readersCount = 0 then Condition.signal noReaders
      ))

    method private doCritical: 'a. 'a lazy_t -> 'a =
      fun action ->
        debug_print (lazy "<doCritical>");
        (try
          Mutex.lock mutex;
          let res = Lazy.force action in
          Mutex.unlock mutex;
          debug_print (lazy "</doCritical>");
          res
        with e ->
          Mutex.unlock mutex;
          raise e);

    method private doReader: 'a. 'a lazy_t -> 'a =
      fun action ->
        debug_print (lazy "<doReader>");
        let cleanup () =
          self#decrReadersCount;
          self#signalNoReaders
        in
        self#incrReadersCount;
        let res = (try Lazy.force action with e -> (cleanup (); raise e)) in
        cleanup ();
        debug_print (lazy "</doReader>");
        res

      (* TODO may starve!!!! is what we want or not? *)
    method private doWriter: 'a. 'a lazy_t -> 'a =
      fun action ->
        debug_print (lazy "<doWriter>");
        self#doCritical (lazy (
          while readersCount > 0 do
            Condition.wait noReaders mutex
          done;
          let res = Lazy.force action in
          debug_print (lazy "</doWriter>");
          res
        ))

  end

