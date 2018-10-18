(******************************************************************************)
(* PipeCheck: Specifying and Verifying Microarchitectural                     *)
(* Enforcement of Memory Consistency Models                                   *)
(*                                                                            *)
(* Copyright (c) 2018 Yatin Manerkar (Princeton Uni.) & Daniel Lustig (NVIDIA)*)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this library; if not, write to the Free Software        *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  *)
(* USA                                                                        *)
(******************************************************************************)

open Printf
open Unix
open Arg
open BackendLinux
open PipeGraph
open HerdGraph
open Lexer
open Parser
open MicroarchLexer
open MicroarchParser

let uarch_filename = ref ""
let do_reduction = ref true
let ghost_auto = ref false
let max_depth = ref 1000
let isa_mcm = ref "SC"

let update_output_filename s =
  let oc = open_out s in BackendLinux.outfile := oc
let update_uarch_filename s = uarch_filename := s
let update_max_depth n = max_depth := n
let update_verbosity n = BackendLinux.verbosity := n
let update_cp_threshold n = BackendLinux.cpThreshold := n
let unknown_argument s = raise (Arg.Bad ("Unknown argument: " ^ s))
let update_filter_strat n = BackendLinux.filter_strat := n
let update_cex_bound n = BackendLinux.cexBound := n
let update_isa_mcm s = isa_mcm := s
let update_isa_sym n = use_isa_sym := n

let parse_anon s = unknown_argument s

let speclist = [
  ("-o", Arg.String update_output_filename, "Output file (stdout otherwise)");
  ("-m", Arg.String update_uarch_filename, "Microarchitecture model file");
  ("-r", Arg.Clear  do_reduction, "Don't perform transitive reduction");
  ("-d", Arg.Int    update_max_depth, "Max depth for DPLL search");
  ("-c", Arg.Int    update_cp_threshold, "Cross product threshold for distributing ANDs over ORs (default 0, i.e. no distribution)");
  ("-s", Arg.Int    update_isa_sym, "Use memoization (ISA-level symmetry) (default 0 = false)");
  ("-l", Arg.String update_isa_mcm, "ISA-level MCM for PipeProof (valid values are \"SC\" and \"TSO\" (no quotes) )");
  ("-x", Arg.Set    genCex, "Try to generate cyclic counterexample if TC abstraction support proof fails (default is no)");
  ("-b", Arg.Int    update_cex_bound, "Max size of cyclic counterexample to generate (value only used if -x is also provided, default is 10)");
  ("-f", Arg.Int    update_filter_strat, "TC filtering strategy for PipeProof:
    0: filter both before and after applying chain invariants
    1: filter only after applying chain invariants (default)
    2: after applying chain invariants, filter and apply covering sets
    3 (or any other number) : filter and apply covering sets both before and after applying chain invariants");
  ("-v", Arg.Int    update_verbosity, "Set verbosity level:
    0: Default; print final output
    1: + Print all solver decisions
    2: + Print steps between solver decisions
    3: + Print constraint trees
    4: same as 3 for now
    5: + Verbose
    6: + More Verbose
    7: + Really Verbose
    8: + Extremely Verbose")]

let _ = Arg.parse speclist parse_anon "PipeGraph"

let _ =
  if (String.length !uarch_filename = 0)
  then (Arg.usage speclist "PipeGraph";
    raise (Arg.Bad "No microarchitecture model file specified"))
  else ();;

let cleanGhostInstructions h =
  match (PipeGraph.getVirtualAddress h, PipeGraph.getPhysicalAddress h) with
  | (Some va, Some pa) -> [
    {h with intraInstructionID0=0};
    {h with intraInstructionID0=1;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=false}))};
    {h with intraInstructionID0=2;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))}]
  | _ -> raise (Failure "Cleaning non-ghost")

let dirtyGhostInstructions h =
  match (PipeGraph.getVirtualAddress h, PipeGraph.getPhysicalAddress h) with
  | (Some va, Some pa) -> [
    {h with intraInstructionID0=0;
       access=Read(["dirtybit"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=false}))};
    {h with intraInstructionID0=1;
       access=Write(["dirtybit"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))};
    {h with intraInstructionID0=2};
    {h with intraInstructionID0=3;
       access=Read(["ptwalk"], {vtag=10+va.vtag; vindex=0},
         {ptag=PTETag va.vtag; pindex=0},
         PageTableEntry (va.vtag, pa.ptag,
           {accessed=true; dirty=true}))}]
  | _ -> raise (Failure "Cleaning non-ghost")

let rec filter_ghosts_helper program =
  match program with
  | h::t ->
      (match (access h, PipeGraph.getAccessType h) with
      | (Fence _, _) -> h :: filter_ghosts_helper t
      | (FenceVA (_, _), _) -> h :: filter_ghosts_helper t
      | (Read _, []) ->
          cleanGhostInstructions h @ filter_ghosts_helper t
      | (Write _, []) ->
          dirtyGhostInstructions h @ filter_ghosts_helper t
      | (Read _, ["RMW"]) ->
          dirtyGhostInstructions h @ filter_ghosts_helper t
      | (Write _, ["RMW"]) ->
          {h with intraInstructionID0=0} :: filter_ghosts_helper t
      | (_, ["ptwalk"]) -> filter_ghosts_helper t
      | (_, ["dirtybit"]) -> filter_ghosts_helper t
      | (_, ["IRQCheck"]) -> h :: filter_ghosts_helper t
      | (_, ["IPIReceive"]) -> h :: filter_ghosts_helper t
      | (_, ["IPIAck"]) -> h :: filter_ghosts_helper t
      | (_, ["IRET"]) -> h :: filter_ghosts_helper t
      | _ -> raise (Failure "Unknown access type"))
  | [] -> []

let filter_ghosts x =
  PipeGraph.Pair (filter_ghosts_helper (PipeGraph.fst x), PipeGraph.snd x)

let rec n_copies n x =
  if n > 0 then (x :: n_copies (n-1) x) else [x]

let parse_uarch filename num_cores =
  let file_descr = Unix.openfile filename [Unix.O_RDONLY] 0 in
  let channel = Unix.in_channel_of_descr file_descr in
  let lexbuf = Lexing.from_channel channel in
  try
    let pipeline = MicroarchParser.main MicroarchLexer.token lexbuf in
    n_copies num_cores pipeline
  with exn ->
    begin
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let offset = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let token = Lexing.lexeme lexbuf in
      Printf.printf "Microarchitecture parsing error: line %d, offset %d, token %s\n"
        line offset token;
      raise (Failure "Parsing microarchitecture")
    end

let processor =
  let num_cores = 0 in
  let baseline = parse_uarch !uarch_filename num_cores in
  baseline

let isa_mcm_for s =
  match s with
  | "TSO" -> PipeGraph.tSO
  | _ -> PipeGraph.seqConst

let first_observable_graph =
  let graph =
    PipeGraph.evaluateUHBGraphs !max_depth processor (isa_mcm_for !isa_mcm) in

  let observable =
    match graph with
    | PipeGraph.Some (PipeGraph.Pair (g, a)) ->
      (* let stage_names = PipeGraph.stageNames processor in
      let s = PipeGraph.graphvizCompressedGraph "" stage_names g [] in
      List.iter (Printf.fprintf oc "%s") s; *)
      true
    | PipeGraph.None -> false
  in

  let result_string =
    if observable then "// Microarchitecture could not be proven! See end of output file for any failing fragment and/or counterexample." else "// Microarchitecture is correct for all programs!"
  in

  Printf.printf "%s\n" result_string

let _ = first_observable_graph;

print_string "// Done!\n"

