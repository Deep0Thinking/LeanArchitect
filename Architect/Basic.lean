import Lean
import Batteries.Lean.NameMapAttribute


open Lean Elab

namespace Architect

initialize registerTraceClass `blueprint
initialize registerTraceClass `blueprint.debug

/-- The statement or proof of a node. -/
structure NodePart where
  /-- The natural language description of this part. -/
  text : String
  /-- The specified set of nodes that this node depends on, in addition to inferred ones. -/
  uses : Array Name
  /-- The set of nodes to exclude from `uses`. -/
  excludes : Array Name
  /-- Additional LaTeX labels of nodes that this node depends on. -/
  usesLabels : Array String
  /-- The set of labels to exclude from `usesLabels`. -/
  excludesLabels : Array String
  /-- The LaTeX environment to use for this part. -/
  latexEnv : String
deriving Inhabited, Repr, FromJson, ToJson, ToExpr

/-- A theorem or definition in the blueprint graph. -/
structure Node where
  /-- The Lean name of the tagged constant. -/
  name : Name
  /-- The LaTeX label of the node. Multiple nodes can have the same label. -/
  latexLabel : String
  /-- The statement of this node. -/
  statement : NodePart
  /-- The proof of this node. -/
  proof : Option NodePart
  /-- The surrounding environment is not ready to be formalized, typically because it requires more blueprint work. -/
  notReady : Bool
  /-- A GitHub issue number where the surrounding definition or statement is discussed. -/
  discussion : Option Nat
  /-- The short title of the node in LaTeX. -/
  title : Option String
deriving Inhabited, Repr, FromJson, ToJson, ToExpr

structure NodeWithPos extends Node where
  /--
  Whether the node name is in the environment.
  This should always be true for nodes e.g. added by `@[blueprint]`.
  -/
  hasLean : Bool
  /-- The location (module & range) the node is defined in. -/
  location : Option DeclarationLocation
  /-- The file the node is defined in. -/
  file : Option System.FilePath
deriving Inhabited, Repr

def Node.toNodeWithPos (node : Node) : CoreM NodeWithPos := do
  let env ← getEnv
  if !env.contains node.name then
    return { node with hasLean := false, location := none, file := none }
  let module := match env.getModuleIdxFor? node.name with
    | some modIdx => env.allImportedModuleNames[modIdx]!
    | none => env.header.mainModule
  let location := match ← findDeclarationRanges? node.name with
    | some ranges => some { module, range := ranges.range }
    | none => none
  let file ← (← getSrcSearchPath).findWithExt "lean" module
  return { node with hasLean := true, location, file }

/-- Environment extension that stores the nodes of the blueprint. -/
initialize blueprintExt : NameMapExtension Node ←
  registerNameMapExtension Node

namespace LatexLabelToLeanNames

abbrev State := SMap String (Array Name)
abbrev Entry := String × Name

private def addEntryFn (s : State) (e : Entry) : State :=
  match s.find? e.1 with
  | none => s.insert e.1 #[e.2]
  | some ns => s.insert e.1 (ns.push e.2)

end LatexLabelToLeanNames

open LatexLabelToLeanNames in
initialize latexLabelToLeanNamesExt : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addEntryFn
    addImportedFn := fun es => mkStateFromImportedEntries addEntryFn {} es |>.switch
  }

def addLeanNameOfLatexLabel (env : Environment) (latexLabel : String) (name : Name) : Environment :=
  latexLabelToLeanNamesExt.addEntry env (latexLabel, name)

def getLeanNamesOfLatexLabel (env : Environment) (latexLabel : String) : Array Name :=
  latexLabelToLeanNamesExt.getState env |>.findD latexLabel #[]

section ResolveConst

register_option blueprint.ignoreUnknownConstants : Bool := {
  defValue := false,
  descr := "Whether to ignore unknown constants in the `uses` and `proofUses` options of the `blueprint` attribute."
}

/--
Resolves an identifier using `realizeGlobalConstNoOverloadWithInfo`.
Ignores unknown constants if `blueprint.ignoreUnknownConstants` is true (default: false).
-/
def tryResolveConst (id : Ident) : CoreM Name := do
  try
    realizeGlobalConstNoOverloadWithInfo id
  catch ex =>
    if blueprint.ignoreUnknownConstants.get (← getOptions) then
      -- logNamedWarningAt id lean.unknownIdentifier ex.toMessageData
      return id.getId
    else
      throwNamedErrorAt id lean.unknownIdentifier
        "{ex.toMessageData}\n\nThis error can be disabled by `set_option blueprint.ignoreUnknownConstants true`."

end ResolveConst

/-- TODO: remove after lean4#12469 -/
scoped instance {α} [Inhabited α] : Inhabited (Thunk α) := ⟨.mk default⟩

section AutoBlueprint

register_option blueprint.all : Bool := {
  defValue := false,
  descr := "Automatically add all declarations with docstrings to the blueprint."
}

/-- Whether a constant is eligible for auto-blueprinting:
a "real" declaration (theorem, def, opaque, or inductive) that is not auxiliary. -/
private def isAutoEligible (env : Environment) (name : Name) : Bool :=
  if name.isInternalDetail then false
  else match env.find? name with
    | some (.thmInfo _) | some (.defnInfo _) | some (.opaqueInfo _) | some (.inductInfo _) => true
    | _ => false

/-- Create an auto-node from a constant's docstring. Returns `none` if ineligible. -/
def mkAutoNode (env : Environment) (name : Name) : Option Node :=
  if !isAutoEligible env name then none
  else if (blueprintExt.find? env name).isSome then none  -- already explicitly tagged
  else match docStringExt.find? env name with
    | none => none  -- no docstring
    | some doc =>
      let isThm := wasOriginallyTheorem env name
      let statement : NodePart := {
        text := doc.trimAscii.copy
        uses := #[], excludes := #[], usesLabels := #[], excludesLabels := #[]
        latexEnv := if isThm then "theorem" else "definition"
      }
      let proof : Option NodePart := if isThm then some {
        text := "", uses := #[], excludes := #[], usesLabels := #[], excludesLabels := #[]
        latexEnv := "proof"
      } else none
      some { name, latexLabel := name.toString, statement, proof, notReady := false
             discussion := none, title := none }

/-- Look up a blueprint node, falling back to auto-node creation when `blueprint.all` is set. -/
def findBlueprintNode? (env : Environment) (opts : Options) (name : Name) : Option Node :=
  (blueprintExt.find? env name).orElse fun () =>
    if blueprint.all.get opts then mkAutoNode env name else none

/-- Check if a name is a blueprint node (explicit or auto). -/
def isBlueprintNode (env : Environment) (opts : Options) (name : Name) : Bool :=
  (findBlueprintNode? env opts name).isSome

/-- Get all blueprint nodes from an imported module.
Auto-nodes are NOT included for imported modules — `blueprint.all` only affects the current file. -/
def getModuleBlueprintNodes (env : Environment) (_opts : Options) (modIdx : ModuleIdx) :
    Array (Name × Node) :=
  blueprintExt.getModuleEntries env modIdx

/-- Get all blueprint nodes from the current file (not yet imported), including auto-nodes. -/
def getLocalBlueprintNodes (env : Environment) (opts : Options) : Array (Name × Node) :=
  let explicit := (blueprintExt.getEntries env).toArray
  if !blueprint.all.get opts then explicit
  else
    -- Find constants in env but not in any imported module
    let autoNodes := env.constants.fold (init := #[]) fun acc name _ =>
      if env.getModuleIdxFor? name |>.isSome then acc  -- from an import
      else match mkAutoNode env name with
        | some node => acc.push (name, node)
        | none => acc
    explicit ++ autoNodes

end AutoBlueprint

end Architect
