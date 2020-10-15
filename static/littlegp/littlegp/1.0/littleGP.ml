(*
 * File: "littleGP.ml"
 *
 * This program is a genetic programming system built in Objective Caml. It was
 * adapted from "Little LISP" computer code for Genetic Programming as contained
 * in 1992 book Genetic Programming by John R. Koza.
 *
 * to compile:
 *    ocamlc -o littleGP littleGP.ml
 * or
 *    ocamlopt -o littleGP littleGP.ml
 *
 *
 * @begin[license]
 * Copyright (C) 2007 Alexsandro Santos Soares
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; version 2
 * of the License.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 *
 * Author: Alexsandro Santos Soares @email{a_s_soares at yahoo dot com}
 *
 * @end[license]
 *)

open List

type tree = Add   of tree   * tree |
            Sub   of tree   * tree |
            Mul   of tree   * tree |
            Div   of tree   * tree |
            Sin   of tree          |
            Cos   of tree          |
            Var   of string        |
            Float of float         |
            Int   of float         |
            Nil


type functions = FADD |
                 FSUB |
                 FMUL |
                 FDIV |
                 FSIN |
                 FCOS

type function_set = functions * int list

type terminal_set = TVAR of string list | TFLOAT | TINT

type ind = { length: int
           ; tree:   tree
           }


type individual = { mutable program               : tree
                  ; mutable standardized_fitness  : float
                  ; mutable adjusted_fitness      : float
                  ; mutable normalized_fitness    : float
                  ; mutable hits                  : int
                  }


type method_of_selection = Tournament
                         | Fitness_Proportionate_With_Over_Selection
                         | Fitness_Proportionate

type method_of_generation = Grow | Full | Ramped_Half_And_Half

(* The number of fitness cases                                               *)
let number_of_fitness_cases = ref 0

(* The maximum depth for individuals of the initial random generation        *)
let max_depth_for_new_individuals = ref 0

(* The maximum depth of new individuals created by crossover                 *)
let max_depth_for_individuals_after_crossover = ref 0

(* The fraction of the population that will experience fitness proportionate
   reproduction (with reselection) during each generation                    *)
let fitness_proportionate_reproduction_fraction = ref 0.0

(* The fraction of the population that will experience crossover at any point
   in the tree (including terminals) during each generation                  *)
let crossover_at_any_point_fraction = ref 0.0

(* The fraction of the population that will experience crossover at a function
   (internal) point in the tree during each generation.                      *)
let crossover_at_function_point_fraction = ref 0.0

(* The maximum depth of new subtrees created by mutation                     *)
let max_depth_for_new_subtrees_in_mutants = ref 0

(* The method of selecting individuals in the population.
   Either :fitness_proportionate, :tournament
   or :fitness_proportionate_with_over_selection.                            *)
let method_of_selection = ref Tournament

(* Can be any one of :grow, :full, :ramped_half_and_half                     *)
let method_of_generation = ref Grow

(* The seed for the Park_Miller congruential randomizer.                     *)
let seed = ref 0

(* The best individual found during this run.                                *)
let best_of_run_individual = ref  { program     = Int 0.0
                                  ; standardized_fitness  = max_float
                                  ; adjusted_fitness      = max_float
                                  ; normalized_fitness    = max_float
                                  ; hits                  = 0
                                  }

(* The generation at which the best_of_run individual was found.             *)
let generation_of_best_of_run_individual = ref 0

(* The Protected Division Function *)
let (%) numerator denominator =
  if (denominator = 0.0) then 1.0 else (numerator /. denominator)

(* The hash table to save values for all variables used in the problem.      *)
let env = Hashtbl.create 10;;

let rec eval tree =
  match tree with
  | Add (x,y) -> (eval x) +. (eval y)
  | Sub (x,y) -> (eval x) -. (eval y)
  | Mul (x,y) -> (eval x) *. (eval y)
  | Div (x,y) -> (eval x) % (eval y)
  | Sin   x   -> sin (eval x)
  | Cos   x   -> cos (eval x)
  | Var   x   -> Hashtbl.find env x
  | Float x   -> x
  | Int   x   -> x
  | Nil       -> raise (Failure "not defined")


(* Returns the depth of the deepest branch of the tree (program). *)
let rec max_depth_of_tree tree =
  match tree with
  | Add (x,y)
  | Sub (x,y)
  | Mul (x,y)
  | Div (x,y) -> 1 + max (max_depth_of_tree x) (max_depth_of_tree y)
  | Sin  x    -> 1 + max_depth_of_tree x
  | Cos  x    -> 1 + max_depth_of_tree x
  | Var   _
  | Float _
  | Int   _   -> 1
  | Nil       -> raise (Failure "not defined")


(* Given the old and new males and females from a crossover
operation check to see whether we have exceeded the maximum
allowed depth. If either of the new individuals has exceeded
the maxdepth then the old individual is used.
*)

let validate_crossover male new_male female new_female =
  let male_depth   = max_depth_of_tree new_male
  and female_depth = max_depth_of_tree new_female in
  let male = if ((male_depth = 1) ||
                 (male_depth > !max_depth_for_individuals_after_crossover))
             then male
             else new_male
  and female = if ((female_depth = 1) ||
                   (female_depth > !max_depth_for_individuals_after_crossover))
               then female
               else new_female
  in
    (male,female)


(* Chooses a random terminal from the terminal set.
  If the terminal chosen is the ephemeral Floating Point Random Constant,
  then a floating_point single precision random constant is created in the
  range _5.0_>5.0.
  If an Integer Random Constant is chosen then an integer random constant is
  generated in the range _10 to +10. *)
let choose_from_terminal_set terminal_set =
  let choice = nth terminal_set (Random.int (length terminal_set)) in
    match choice with
    | TFLOAT    -> Float (-.5.0 +. Random.float 10.0)
    | TINT      -> Int (float (-10 + Random.int 20))
    | TVAR lvar -> let new_choice = Random.int (length lvar) in
                     Var (nth lvar new_choice)

let rec cons f args =
  match f with
    FADD -> Add (hd args, hd (tl args))
  | FSUB -> Sub (hd args, hd (tl args))
  | FMUL -> Mul (hd args, hd (tl args))
  | FDIV -> Div (hd args, hd (tl args))
  | FSIN -> Sin (hd args)
  | FCOS -> Cos (hd args)


(* Creates the argument list for a node in the tree. Number_Of_Arguments is
   the number of arguments still remaining to be created. Each argument is
   created in the normal way using Create_Individual_Program.*)
let rec create_arguments_for_function number_of_arguments function_set
                                      terminal_set allowable_depth full =
  if (number_of_arguments = 0)
  then  []
  else
     (create_individual_program function_set terminal_set allowable_depth false
     full) ::
     create_arguments_for_function (number_of_arguments - 1) function_set
                                   terminal_set allowable_depth full

(* Creates a program recursively using the specified functions and terminals.
   Argument map is used to determine how many arguments each function in the
   function set is supposed to have if it is selected. Allowable depth is
   the remaining depth of the tree we can create, when we hit zero we will
   only select terminals. Top_node_p is true only when we are being called as
   the top node in the tree. This allows us to make sure that we always put a
   function at the top of the tree. Full_p indicates whether this individual
   is to be maximally bushy or not.
*)
and create_individual_program function_set terminal_set allowable_depth
                              top_node full =
  if (allowable_depth <= 0 ) then
    (* We've reached maxdepth, so just pack a terminal.*)
    choose_from_terminal_set terminal_set
  else if (full || top_node) then
    (* We are the top node or are a full tree, so pick only a function. *)
    let choice   = Random.int (length function_set) in
    let fn,arity = nth function_set choice in
    let args = create_arguments_for_function arity function_set
                                             terminal_set (allowable_depth - 1)
                                             full
    in
      cons fn args
  else
    (* choose one from the bag of functions and terminals. *)
    let choice   = Random.int (length terminal_set + length function_set) in
      if ( choice < length function_set) then
        (* We chose a function, so pick it out and go on creating the tree down
           from here. *)
        let fn,arity = nth function_set choice     in
        let args = create_arguments_for_function arity function_set
                                   terminal_set        (allowable_depth - 1)
                                   full
        in
          cons fn args
      else
        (* We chose an atom, so pick it out. *)
        choose_from_terminal_set terminal_set
;;


(* Counts the number of function (internal) points in the program. *)
let rec count_function_points program =
  match program with
  | Add (x,y)
  | Sub (x,y)
  | Mul (x,y)
  | Div (x,y) -> 1 + (count_function_points x) + (count_function_points y)
  | Sin  x
  | Cos  x    -> 1 + (count_function_points x)
  | Var   _
  | Float _
  | Int   _
  | Nil       -> 0

(* Counts the number of points in the tree (program). This includes functions
   as well as terminals. *)
let rec count_crossover_points program =
  match program with
  | Add (x,y)
  | Sub (x,y)
  | Mul (x,y)
  | Div (x,y) -> 1 +  (count_crossover_points x) + (count_crossover_points y)
  | Sin  x
  | Cos  x    -> 1 + (count_function_points x)
  | Var   _
  | Float _
  | Int   _   -> 1
  | Nil       -> 0

(* Given a tree or subtree, a pointer to that tree/subtree and an index return
   the component subtree that is labeled with an point that is numbered by
   Point. We number left to right, depth first. *)
let rec get_subtree count_function tree point =
  if (point = 0) then
    tree
  else
    match tree with
    | Add (x,y)
    | Sub (x,y)
    | Mul (x,y)
    | Div (x,y) ->
        let left_points = count_function x in
          if (point <= left_points) then
            get_subtree (count_function) x (point - 1)
          else
            get_subtree (count_function) y (point - (left_points + 1))
    | Sin  x
    | Cos  x    -> get_subtree (count_function) x (point - 1)
    | _   -> failwith ("The number of nodes in a tree branch is less than " ^
                        string_of_int point)

let rec copy_tree tree =
    match tree with
    | Add (x,y) -> Add (copy_tree x, copy_tree y)
    | Sub (x,y) -> Sub (copy_tree x, copy_tree y)
    | Mul (x,y) -> Mul (copy_tree x, copy_tree y)
    | Div (x,y) -> Div (copy_tree x, copy_tree y)
    | Sin  x    -> Sin (copy_tree x)
    | Cos  x    -> Cos (copy_tree x)
    | Var   x   -> Var x
    | Float x   -> Float x
    | Int   x   -> Int x
    | Nil       -> Nil


let rec replace' count_function left right fragment point =
  let left_points = count_function left in
    if (point <= left_points) then
      (replace count_function left fragment (point - 1), right)
     else
      (left, replace count_function right fragment (point - (left_points + 1)))

and replace count_function tree fragment point =
  if (point = 0) then fragment
  else
    match tree with
        Add (left,right) ->
         let left',right' = replace' (count_function) left right fragment point
         in  Add (left',right')
      | Sub (left,right) ->
         let left',right' = replace' (count_function) left right fragment point
         in  Sub (left',right')
      | Mul (left,right) ->
         let left',right' = replace' (count_function) left right fragment point
         in  Mul (left',right')
      | Div (left,right) ->
         let left',right' = replace' (count_function) left right fragment point
         in  Div (left',right')
      | Sin left ->
         let left', _ = replace' (count_function) left (Nil) fragment point
         in  Sin (left')
      | Cos left ->
         let left', _ = replace' (count_function) left (Nil) fragment point
         in  Cos (left')
      | Var   _
      | Float _
      | Int   _
      | Nil     -> failwith ("replace: The number of nodes in a tree branch \
                              is less than " ^ string_of_int point)


(* Performs crossover on the two programs at a point in the trees. *)
let crossover_at count_function male female =
  (* Pick the points in the respective trees on which to perform the crossover.
  *)
  let male_point      = Random.int (count_function male)
  and female_point    = Random.int (count_function female) in
  let male_fragment   = get_subtree count_function male   male_point
  and female_fragment = get_subtree count_function female female_point  in
  (* Create the new individuals by smashing in the (copied) subtree from the
     old individual. *)
  let new_male        = replace (count_function) male   female_fragment
  male_point
  and new_female      = replace (count_function) female male_fragment
  female_point in
    (* Make sure that the new individuals aren't too big. *)
     validate_crossover male new_male female new_female

(* Performs crossover on the two programs at a function (internal) point in
   the trees. *)
let crossover_at_function_points male female =
  crossover_at (count_function_points) male female

(* Performs crossover on the programs at any point in the trees. *)
let crossover_at_any_points male female =
  crossover_at (count_crossover_points) male female

(* Mutates the argument program by picking a random point in the tree and
   substituting in a brand new subtree created in the same way that we create
   the initial random population. *)
let mutate program function_set terminal_set =
  (* Pick the mutation point *)
  let mutation_point = Random.int (count_crossover_points program)
  (* Create a brand new subtree. *)
  and new_subtree = create_individual_program function_set terminal_set
                           !max_depth_for_new_subtrees_in_mutants true false in
  let new_program = copy_tree program in
    (* Smash in the new subtree. *)
    replace (count_crossover_points) new_program new_subtree mutation_point


(* Transform a tree in a printable string in infix notation. *)
let rec tree_to_string tree =
  match tree with
    Add (x,y) -> "(" ^ (tree_to_string x) ^ " + " ^ (tree_to_string y) ^ ")"
  | Sub (x,y) -> "(" ^ (tree_to_string x) ^ " - " ^ (tree_to_string y) ^ ")"
  | Mul (x,y) -> "(" ^ (tree_to_string x) ^ " * " ^ (tree_to_string y) ^ ")"
  | Div (x,y) -> "(" ^ (tree_to_string x) ^ " % " ^ (tree_to_string y) ^ ")"
  | Sin   x   -> "sin(" ^ (tree_to_string x) ^ ")"
  | Cos   x   -> "cos(" ^ (tree_to_string x) ^ ")"
  | Var   x   -> x
  | Float x
  | Int   x   -> string_of_float x
  | Nil       -> ""


(* Prints out the best-of-run individual. *)
let report_on_run () =
  print_string ("\nThe best-of-run individual program for this run was found \
                 on generation " ^
                 (Printf.sprintf "%d" !generation_of_best_of_run_individual)
                 ^
                 "\nand had a standardized fitness measure of " ^
                 (Printf.sprintf "%g and %d hits.\nIt was %s\n"
                           !best_of_run_individual.standardized_fitness
                           !best_of_run_individual.hits
                           (tree_to_string !best_of_run_individual.program) ))
;;


(*Prints out the best individual at the end of each generation *)
let report_on_generation generation_number population =
  let best_individual = population.(0)
  and size_of_population = Array.length population
  (* Add up all of the standardized fitnesses to get average *)
  and sum = Array.fold_left
              (fun x y -> x +. y.standardized_fitness) 0.0 population
  in
    print_string ((Printf.sprintf
                     "\nGeneration %d: Average standardized-fitness = %g"
                      generation_number (sum /. (float size_of_population))) ^
                  "\nThe best individual program of the population had a \
                   standardized " ^
                  (Printf.sprintf
                     "fitness measure of %g and %d hits.\nIt was %s\n"
                     best_individual.standardized_fitness
                     best_individual.hits
                     (tree_to_string best_individual.program)
                 ))
;;


(* Lists the parameter settings for this run. *)
let describe_parameters_for_run maximum_generations size_of_population =
  print_string
  ( "\nParameters used for this run =============================" ^
    (Printf.sprintf "\nMaximum number of Generations: %d" maximum_generations) ^
    (Printf.sprintf "\nSize of Population: %d" size_of_population) ^
    (Printf.sprintf "\nMaximum depth of new individuals: %d"
                    !max_depth_for_new_individuals) ^
    (Printf.sprintf "\nMaximum depth of new subtrees for mutants: %d"
                    !max_depth_for_new_subtrees_in_mutants) ^
    (Printf.sprintf "\nMaximum depth of individuals after crossover: %d"
                    !max_depth_for_individuals_after_crossover) ^
    (Printf.sprintf "\nFitness_proportionate reproduction fraction: %g"
                    !fitness_proportionate_reproduction_fraction) ^
    (Printf.sprintf "\nCrossover at any point fraction: %g"
                    !crossover_at_any_point_fraction) ^
    (Printf.sprintf "\nCrossover at function points fraction: %g"
                    !crossover_at_function_point_fraction) ^
    (Printf.sprintf "\nNumber of fitness cases: %d" !number_of_fitness_cases) ^
    (Printf.sprintf "\nSelection method: %s"
             (match !method_of_selection with
                Tournament -> "tournament"
              | Fitness_Proportionate_With_Over_Selection ->
                 "fitness proportionate with over selection"
              | Fitness_Proportionate -> "fitness proportionate")
    ) ^
    (Printf.sprintf "\nGeneration method: %s"
             (match !method_of_generation with
              | Grow -> "grow"
              | Full -> "full"
              | Ramped_Half_And_Half -> "ramped half-and-half")

    ) ^
    (Printf.sprintf "\nRandomizer seed: %d\n" !seed)
  )


(* Creates the population. This is an array of size size-of-population that is
   initialized to contain individual records. The Program slot of each
   individual is initialized to a suitable random program except for the first
   programs, where N = (length seeded-programs). For these first N individuals
   the individual is initialized with the respective seeded program. This is
   very useful in debugging. *)
let create_population size_of_population function_set terminal_set
seeded_programs =
  (* Used to guarantee that all generation 0 individuals are unique *)
  let generation_0_uniquifier_table =  Hashtbl.create size_of_population
  and population = Array.init size_of_population
                              (fun _ -> { program              = Int 0.0
                                        ; standardized_fitness = 0.0
                                        ; adjusted_fitness     = 0.0
                                        ; normalized_fitness   = 0.0
                                        ; hits                 = 0
                                        } )
  and minimum_depth_of_trees      = ref 1
  and attempts_at_this_individual = ref 0
  and full_cycle_p                = ref false
  and individual_index = ref 0 in
    while ( !individual_index < size_of_population) do
      if ((!individual_index mod
           (max 1 (!max_depth_for_new_individuals - !minimum_depth_of_trees))) =
           0)
      then
        full_cycle_p := not !full_cycle_p;
      let new_program =
        if (!individual_index < (length seeded_programs)) then
          (* Pick a seeded individual *)
          nth seeded_programs !individual_index
        else
          (* Create a new random program.*)
          create_individual_program function_set terminal_set
            (match !method_of_generation with
               Full | Grow -> !max_depth_for_new_individuals
             | Ramped_Half_And_Half -> !minimum_depth_of_trees +
               (!individual_index mod (!max_depth_for_new_individuals - !
               minimum_depth_of_trees)))
            true
            (match !method_of_generation with
               Full -> true
             | Grow -> false
             | Ramped_Half_And_Half -> !full_cycle_p)
      in
        (* Check if we have already created this program. If not then store it
           and move on. If we have then try again. *)
        if (!individual_index < (length seeded_programs)) then
          begin
            population.(!individual_index).program <- new_program;
            incr individual_index
          end
        else
          if (not (Hashtbl.mem generation_0_uniquifier_table new_program)) then
            begin
              population.(!individual_index).program <- new_program;
              Hashtbl.add generation_0_uniquifier_table new_program true;
              attempts_at_this_individual := 0;
              incr individual_index
            end
        else
          if (!attempts_at_this_individual > 20) then
            begin
              (* Then this depth has probably filled up, so bump the depth
                 counter *)
              incr minimum_depth_of_trees;
              (* Bump the max depth too to keep in line with new minimum. *)
              max_depth_for_new_individuals := max !
              max_depth_for_new_individuals !
              minimum_depth_of_trees;
            end
        else
          incr attempts_at_this_individual
    done;
    (* Return the population that we've just created. *)
    population
;;

(* Picks a random number between 0.0 and 1.0 biased using the over-selection
   method. *)
let random_floating_point_number_with_over_selection population =
  let pop_size = Array.length population in
    if (pop_size < 1000) then
      raise (Failure (Printf.sprintf
                      "A population size of %d is too small for over-selection."
                      pop_size));
  let boundary = 320.0 /. (float pop_size) in
    (* The boundary between the over and under selected parts. *)
    if ((Random.float 1.0) < 0.8) then
      (* 80% are in the over-selected part *)
      Random.float boundary
    else
      boundary +. (Random.float (1.0 -. boundary))

(* Picks two individuals from the population at random and returns the better
   one. *)
let find_individual_using_tournament_selection population =
  let individual_a = population.(Random.int (Array.length population))
  and individual_b = population.(Random.int (Array.length population))
  in
    if (individual_a.standardized_fitness < individual_b.standardized_fitness)
    then
      individual_a.program
    else
      individual_b.program
;;


(* Finds an individual in the specified population whose normalized fitness is
   greater than the specified value. All we need to do is count along the
   population from the beginning adding up the fitness until we get past the
   specified point. *)
let find_fitness_proportionate_individual after_this_fitness population =
  let sum_of_fitness  = ref 0.0
  and population_size = Array.length population in
  let index_of_selected_individual =
    let index = ref 0 in
    while ((!index < population_size) && (!sum_of_fitness < after_this_fitness))
    do
      (* Sum up the fitness values *)
      sum_of_fitness := !sum_of_fitness +. population.(!index).
      normalized_fitness;
      incr index
    done;
    if (!index >= population_size) then
      (Array.length population) - 1
    else
      !index - 1
  in
    population.(index_of_selected_individual).program
;;


(* Finds an individual in the population according to the defined selection
   method. *)
let find_individual population =
  match !method_of_selection with
    Tournament -> find_individual_using_tournament_selection population
  | Fitness_Proportionate_With_Over_Selection ->
      find_fitness_proportionate_individual
       (random_floating_point_number_with_over_selection population) population
  | Fitness_Proportionate ->
      find_fitness_proportionate_individual (Random.float 1.0) population

(* Controls the actual breeding of the new population. Loops through the
   population executing each operation (e.g., crossover, fitness-proportionate
   reproduction, mutation) until it has reached the specified fraction. The new
   programs that are created are stashed in new-programs until we have exhausted
   the population, then we copy the new individuals into the old ones, thus
   avoiding consing a new bunch of individuals. *)
let breed_new_population population new_programs function_set terminal_set =
  let population_size = Array.length population
  and index     = ref 0
  and fraction  = ref 0.0 in
    while (!index < population_size) do
      let individual_1 = find_individual population in
        if ((!index < (population_size - 1)) &&
            (!fraction < (!crossover_at_function_point_fraction +.
                          !crossover_at_any_point_fraction)))
        then
          begin
            let new_male, new_female =
                (if (!fraction < !crossover_at_function_point_fraction) then
                    crossover_at_function_points
                 else
                     crossover_at_any_points) individual_1 (find_individual
                     population)
            in
              new_programs.(!index) <- new_male;
              incr index;
              new_programs.(!index) <- new_female;
              incr index;
          end
        else
          if (!fraction < (!fitness_proportionate_reproduction_fraction +.
                           !crossover_at_function_point_fraction        +.
                           !crossover_at_any_point_fraction)) then
            begin
              new_programs.(!index) <- individual_1;
              incr index
            end
          else
            begin
              new_programs.(!index) <- mutate individual_1 function_set
              terminal_set;
              incr index
            end;
      fraction := (float !index) /. (float population_size)
    done;
    for index = 0 to population_size - 1 do
      population.(index).program <- new_programs.(index)
    done
;;


(* Clean out the statistics in each individual in the population. This is not
   strictly necessary, but it helps to avoid confusion that might be caused if,
   for some reason, we land in the debugger and there are fitness values
   associated with the individual records that actually matched the program that
   used to occupy this individual record.
 *)
let zeroize_fitness_measures_of_population population =
  for individual_index = 0 to Array.length population - 1 do
    let individual = population.(individual_index) in
      individual.standardized_fitness <- 0.0;
      individual.adjusted_fitness     <- 0.0;
      individual.normalized_fitness   <- 0.0;
      individual.hits                 <- 0
  done
;;

(* Loops over the individuals in the population evaluating and recording the
   fitness and hits. *)
let evaluate_fitness_of_population population fitness_cases fitness_function =
  for individual_index = 0 to Array.length population - 1 do
    let individual = population.(individual_index) in
    let standardized_fitness, hits = fitness_function individual.program
    fitness_cases in
      (* Record fitness and hits for this individual. *)
      individual.standardized_fitness <- standardized_fitness;
      individual.hits                 <- hits
  done
;;


(* Computes the normalized and adjusted fitness of each individual in the
   population. *)
let normalize_fitness_of_population population =
  let sum_of_adjusted_fitnesses = ref 0.0 in
    for individual_index = 0 to Array.length population - 1 do
      let individual = population.(individual_index) in
        (* Set the adjusted fitness. *)
        individual.adjusted_fitness <- 1.0 /.
                                      (1.0 +. individual.standardized_fitness);
        (* Add up the adjusted fitnesses so that we can normalize them. *)
        sum_of_adjusted_fitnesses := !sum_of_adjusted_fitnesses +.
                                     individual.adjusted_fitness
    done;
    for individual_index = 0 to Array.length population - 1 do
      let individual = population.(individual_index) in
        individual.normalized_fitness <- individual.adjusted_fitness /.
                                         !sum_of_adjusted_fitnesses
    done
;;

(* Sorts the population according to descending order of normalized fitness.
   The population array is destructively modified. *)
let sort_population_by_fitness population =
  let compare ind1 ind2 =
    if (ind1.normalized_fitness > ind2.normalized_fitness) then -1 else
    if (ind1.normalized_fitness < ind2.normalized_fitness) then  1 else 0
  in
    Array.sort compare population
;;


(* Generates a copy of the individual pasted as argument *)
let copy_individual individual = {individual with program = individual.program}

(* Loops until the user's termination predicate says to stop. *)
let execute_generations population new_programs fitness_cases
        maximum_generations fitness_function termination_predicate function_set
        terminal_set =
  let current_generation = ref 0
  and best_of_generation = ref population.(0) in
    while (termination_predicate !current_generation maximum_generations
                                 !best_of_generation.standardized_fitness
                                 !best_of_generation.hits) do
      if (!current_generation > 0) then
        (* Breed the new population to use on this generation
           (except gen 0, of course).
        *)
        breed_new_population population new_programs function_set terminal_set;
      (* Clean out the fitness measures. *)
      zeroize_fitness_measures_of_population population;
      (* Measure the fitness of each individual. Fitness values are stored in
         the individuals themselves *)
      evaluate_fitness_of_population population fitness_cases fitness_function;
      (* Normalize fitness in preparation for crossover, etc. *)
      normalize_fitness_of_population population;
      (* Sort the population so that the roulette wheel is easy. *)
      sort_population_by_fitness population;
      (* Keep track of best-of-run individual *)
      best_of_generation := population.(0);
      if (!best_of_run_individual.standardized_fitness  >
          !best_of_generation.standardized_fitness      ) then
        begin
          best_of_run_individual := copy_individual !best_of_generation;
          generation_of_best_of_run_individual := !current_generation
        end;
      (* Print out the results for this generation. *)
      report_on_generation !current_generation population;
      incr current_generation
    done
 ;;


let run_genetic_programming_system problem_function seed' maximum_generations
      size_of_population seeded_programs =
      (* seeded_programs is a list with the arguments rest *)
  (* Check validity of some arguments *)
  if (maximum_generations < 0) then
    failwith ("Maximum_generations must be a non_negative integer, not " ^
              string_of_int maximum_generations);
  if (size_of_population <= 0) then
    failwith ("Size_Of_Population must be a positive integer, not " ^
               string_of_int size_of_population);
  (* Set the global randomizer seed. *)
  seed := seed';
  Random.init !seed;
  (* Initialize best-of-run recording variables *)
  generation_of_best_of_run_individual := 0;
  best_of_run_individual := { program     = Int 0.0
                            ; standardized_fitness  = max_float
                            ; adjusted_fitness      = max_float
                            ; normalized_fitness    = max_float
                            ; hits                  = 0
                            };
  (* Get the six problem-specific functions needed to specify this problem as
     returned by a call to problem-function *)
  let (function_set_creator, terminal_set_creator, fitness_cases_creator,
       fitness_function,     parameter_definer,    termination_predicate) =
       problem_function ()
  in
    (* Set up the parameters using parameter-definer *)
    parameter_definer ();
    (* Print out parameters report *)
    describe_parameters_for_run maximum_generations size_of_population;
    (* Get the function set and its associated argument map *)
    let function_set = function_set_creator ()
    (* Set up the terminal-set using terminal-set-creator *)
    and terminal_set = terminal_set_creator () in
    (* Create the population *)
    let population = create_population size_of_population function_set
    terminal_set
    seeded_programs
    (* Define the fitness cases using the fitness-cases-creator function *)
    and fitness_cases = fitness_cases_creator ()
    (* New_Programs is used in the breeding of the new population. Create it
       here to reduce consing. *)
    and new_programs = Array.init size_of_population (fun i -> Int (float i)) in
      (* Now run the Genetic Programming Paradigm using the fitness_function and
         termination_predicate provided *)
      execute_generations population new_programs fitness_cases
         maximum_generations fitness_function termination_predicate
         function_set terminal_set;
      (* Finally print out a report *)
      report_on_run ();
      (* Return the population and fitness cases (for debugging) *)
      (population, fitness_cases)
;;

(******************************************************************************)

(* Transform a tree in a form printable with LaTex using the style
   parsetree.sty. *)
let tree_to_tex tree =
  let rec to_tex tree =
      match tree with
        Add (x,y) -> Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\t%s\n\\ptend"
        "$+$"
                                    (to_tex x) (to_tex y)
      | Sub (x,y) -> Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\t%s\n\\ptend"
      "$-$"
                                    (to_tex x) (to_tex y)
      | Mul (x,y) ->
          Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\t%s\n\\ptend" "$\\times$"
                          (to_tex x) (to_tex y)
      | Div (x,y) -> Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\t%s\n\\ptend"
      "\\%"
                                    (to_tex x) (to_tex y)
      | Sin x     -> Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\\ptend" "sin"
      (to_tex x)
      | Cos x     -> Printf.sprintf "\\ptbeg \\ptnode{%s}\n\t%s\n\\ptend" "cos"
      (to_tex x)
      | Var   x   -> Printf.sprintf "\\ptleaf{%s}"   x
      | Float x   -> Printf.sprintf "\\ptleaf{%.3f}" x
      | Int   x   -> Printf.sprintf "\\ptleaf{%d}"   (truncate x)
      | Nil       -> ""
  in
    Printf.sprintf "\\bigskip\\ptbegtree\n%s\\ptendtree\n" (to_tex tree)


(* Given a population, this prints it out (for debugging) *)
let print_population population =
  for index = 0 to Array.length population - 1 do
    let individual = population.(index) in
      print_string (Printf.sprintf "\n%d %g %g %s" index
      individual.standardized_fitness individual.normalized_fitness
      (tree_to_string individual.program))
  done
;;

(******************************************************************************)

let define_function_set_for_REGRESSION () = [(FADD,2); (FSUB,2) ; (FMUL,2);
     (FDIV,2); (FSIN,2)]

let define_terminal_set_for_REGRESSION () = [TVAR ["x"]; TFLOAT; TINT]


type regression_fitness_case = { independent_variable : float
                               ; target               : float
                               }

let define_fitness_cases_for_REGRESSION () =
  let fitness_cases = Array.init !number_of_fitness_cases
                          (fun index ->
                            let x = ( float index /.
                                      float !number_of_fitness_cases) in
                              { independent_variable = x;
                                target = 0.5 *. x *. x
                              }
                          )
  in
    fitness_cases
;;

let regression_wrapper (result_from_program : float) = result_from_program

let evaluate_standardized_fitness_for_REGRESSION program fitness_cases =
  let raw_fitness           = ref 0.0
  and hits                  = ref 0     in
    for index = 0 to !number_of_fitness_cases - 1 do
      let this_fitness_case = fitness_cases.(index) in
      let x                 = this_fitness_case.independent_variable
      and target_value      = this_fitness_case.target         in
      Hashtbl.replace env "x" x;
      let value_from_program = regression_wrapper (eval program) in
      let difference        = abs_float (target_value -. value_from_program) in
        raw_fitness := !raw_fitness +. difference;
        if (difference < 0.01) then incr hits
    done;
    let standardized_fitness  = !raw_fitness in
      (standardized_fitness, !hits)

let define_parameters_for_REGRESSION () =
  number_of_fitness_cases                     := 10;
  max_depth_for_new_individuals               := 6;
  max_depth_for_individuals_after_crossover   := 17;
  fitness_proportionate_reproduction_fraction := 0.1;
  crossover_at_any_point_fraction             := 0.2;
  crossover_at_function_point_fraction        := 0.7;
  max_depth_for_new_subtrees_in_mutants       := 4;
  method_of_selection                         := Fitness_Proportionate;
  method_of_generation                        := Ramped_Half_And_Half
;;


let define_termination_criterion_for_REGRESSION (current_generation : int)
      maximum_generations (best_standardized_fitness : float) best_hits =
  (current_generation < maximum_generations) &&
  (best_hits < !number_of_fitness_cases)

let regression () =
  (define_function_set_for_REGRESSION,
   define_terminal_set_for_REGRESSION,
   define_fitness_cases_for_REGRESSION,
   (evaluate_standardized_fitness_for_REGRESSION),
   define_parameters_for_REGRESSION,
   (define_termination_criterion_for_REGRESSION)
  )
;;


let test_REGRESSION () =
  run_genetic_programming_system
    (regression)          (* problem function                             *)
    1                     (* seed for random number generator             *)
    31                    (* maximum number of generations                *)
    200                   (* size of population                           *)
    []                    (* Seeded programs to add to initial population.
                             Ex:
                                 [Mul(Float 0.5, Mul (Var "x",Var "x"))]  *)


let _ = if not (!Sys.interactive) then ignore (test_REGRESSION ())


