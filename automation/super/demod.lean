import .clause_ops .prover_state
open tactic monad

namespace super

meta def flip_eq' (c : clause) : tactic clause := do
guard $ c↣num_lits = 1,
cs ← on_right_at' c 0 (λhyp, do
  pr ← mk_app ``eq.symm [hyp],
  return [([], pr)]),
returnopt $ cs↣nth 0

meta def flip_eq (c : derived_clause) : tactic derived_clause := do
c' ← flip_eq' c↣c,
return { c with c := c' }

variable gt : expr → expr → bool

meta def get_demods (cs : list derived_clause) : prover (list derived_clause) :=
liftM list.join $ forM cs $ λa,
match a↣c↣get_lits with
| [(clause.literal.right formula)] :=
  match formula↣is_eq with
  | some (lhs, rhs) :=
    if gt rhs lhs then do
      a ← ♯ flip_eq a,
      return [a]
    else if gt lhs rhs then
      return [a]
    else return []
  | _ := return []
  end
| _ := return []
end

meta def get_demods_active : prover (list derived_clause) :=
do active ← get_active, get_demods gt active↣values

-- meta def do_demod 

end super
