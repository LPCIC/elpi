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

(* $Id: extThread.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

let debug = true
let debug_print s = if debug then prerr_endline (Lazy.force s)

exception Can_t_kill of Thread.t * string (* thread, reason *)
exception Thread_not_found of Thread.t

module OrderedPid =
  struct
    type t = int
    let compare = Pervasives.compare
  end
module PidSet = Set.Make (OrderedPid)

 (* perform an action inside a critical section controlled by given mutex *)
let do_critical mutex =
  fun action ->
    try
      Mutex.lock mutex;
      let res = Lazy.force action in
      Mutex.unlock mutex;
      res 
    with e -> Mutex.unlock mutex; raise e

let kill_signal = Sys.sigusr2   (* signal used to kill children *)
let chan = Event.new_channel () (* communication channel between threads *)
let creation_mutex = Mutex.create ()
let dead_threads_walking = ref PidSet.empty
let pids: (Thread.t, int) Hashtbl.t = Hashtbl.create 17

  (* given a thread body (i.e. first argument of a Thread.create invocation)
  return a new thread body which unblock the kill signal and send its pid to
  parent over "chan" *)
let wrap_thread body =
  fun arg ->
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [ kill_signal ]);
    Event.sync (Event.send chan (Unix.getpid ()));
    body arg

(*
(* FAKE IMPLEMENTATION *)
let create = Thread.create
let kill _ = ()
*)

let create body arg =
  do_critical creation_mutex (lazy (
    let thread_t = Thread.create (wrap_thread body) arg in
    let pid = Event.sync (Event.receive chan) in
    Hashtbl.add pids thread_t pid;
    thread_t
  ))

let kill thread_t =
  try
    let pid =
      try
        Hashtbl.find pids thread_t
      with Not_found -> raise (Thread_not_found thread_t)
    in
    dead_threads_walking := PidSet.add pid !dead_threads_walking;
    Unix.kill pid kill_signal
  with e -> raise (Can_t_kill (thread_t, Printexc.to_string e))

  (* "kill_signal" handler, check if current process must die, if this is the
  case exits with Thread.exit *)
let _ =
  ignore (Sys.signal kill_signal (Sys.Signal_handle
    (fun signal ->
      let myself = Unix.getpid () in
      match signal with
      | sg when (sg = kill_signal) &&
                (PidSet.mem myself !dead_threads_walking) ->
          dead_threads_walking := PidSet.remove myself !dead_threads_walking;
          debug_print (lazy "AYEEEEH!");
          Thread.exit ()
      | _ -> ())))

  (* block kill signal in main process *)
let _ = ignore (Unix.sigprocmask Unix.SIG_BLOCK [ kill_signal ])

