import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.CommPresIsoSub
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

section Sets

variable {r J : ℕ} (nL : ZMod J → ℕ)

/- English proof (translation)
Introduce `x hx`. Simplify using `only [NSet, Set.mem_union, Set.mem_setOf_eq] at hx ⊢`. Break down `hx with ⟨l, hl, hlu⟩ | ⟨m, hm, hmu⟩` into its components or cases. Conclude with `Or.inl ⟨l, hl, by omega⟩`. Conclude with `Or.inr ⟨m, hm, by omega⟩`.
-/
theorem NSet_mono (j : ZMod J) {u u' : ℕ} (h : u ≤ u') : NSet (r := r) nL j u ⊆ NSet nL j u' := by
  intro x hx
  simp only [NSet, Set.mem_union, Set.mem_setOf_eq] at hx ⊢
  rcases hx with ⟨l, hl, hlu⟩ | ⟨m, hm, hmu⟩
  · exact Or.inl ⟨l, hl, by omega⟩
  · exact Or.inr ⟨m, hm, by omega⟩

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce `x hx hx'`. Simplify using `only [NSet, Set.mem_union, Set.mem_setOf_eq] at hx hx'`. Apply the tactic sequence `rcases hx with ⟨l, rfl, -⟩ | ⟨m, rfl, -⟩ <;> rcases hx' with ⟨l', e, -⟩ | ⟨m', e, -⟩ <;>`. Conclude with `h (congrArg Sigma.fst e)`.
-/
theorem NSet_disj {j j' : ZMod J} (h : j ≠ j') (u u' : ℕ) : Disjoint (NSet (r := r) nL j u) (NSet nL j' u') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [NSet, Set.mem_union, Set.mem_setOf_eq] at hx hx'
  rcases hx with ⟨l, rfl, -⟩ | ⟨m, rfl, -⟩ <;> rcases hx' with ⟨l', e, -⟩ | ⟨m', e, -⟩ <;>
    exact h (congrArg Sigma.fst e)

end Sets

section Inst

variable (D : Formalism.BasicNotions.D7) {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
  [NeZero J] [NeZero r] (K : ℕ) [NeZero K] [CharZero (KK O)] (Dt : SignedChainData p O r J)

abbrev NIdx := Σ j : ZMod J, Fin (Dt.nL j + r + 1)

def eeN (i : NIdx Dt) : (Fin K → ℤ) → Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :=
  Classical.choose (Formalism.MainNotions.G.Joints.polIsoDecompB_of D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D) (KK O) (TL J Dt.nL r)
    Dt.trueLet K (NSet Dt.nL i.1 i.2.val))

/- English proof (translation)
The claim follows from `Classical.choose_spec (Formalism.MainNotions.G.Joints.polIsoDecompB_of D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D) (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL i.1 i.2.val))`.
-/
theorem eeN_spec (i : NIdx Dt) :
    (∀ mu, IsIsoProj (normE p K Dt i) mu (eeN D K Dt i mu)) ∧
      ∀ G : MvPolynomial (TL J Dt.nL r × Fin K) (KK O), ∃ T : Finset (Fin K → ℤ),
        G = ∑ mu ∈ T, eeN D K Dt i mu G ∧ ∀ mu, eeN D K Dt i mu G ∈ isoSub (normE p K Dt i) mu :=
  Classical.choose_spec (Formalism.MainNotions.G.Joints.polIsoDecompB_of D (Formalism.MainNotions.G.GLWeightTheory.weight_condition_from_integral_form D) (KK O) (TL J Dt.nL r)
    Dt.trueLet K (NSet Dt.nL i.1 i.2.val))

/- English proof (translation)
Establish `hmono : Monotone (fun k : Fin 2 => if k.val = 0 then NSet (r` using `r) Dt.nL j a.val else NSet Dt.nL j b.val) := by`. Introduce `x y hxy`. Establish `hxy' : x.val ≤ y.val` using `hxy`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> first | exact le_refl _ | exact NSet_mono Dt.nL j hab | omega`.

Establish `h` using `((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 2 _ hmono).2 (fun k => if k.val = 0 then eeN D K Dt ⟨j, a⟩ else eeN D K Dt ⟨j, b⟩) (by`. Introduce `k lam`. Distinguish the cases in `hk : k.val = 0`. Simplify using `only [hk, ↓reduceIte]`. Conclude with `(eeN_spec D K Dt ⟨j, a⟩).1 lam`.

Simplify using `only [hk, ↓reduceIte]`. Conclude with `(eeN_spec D K Dt ⟨j, b⟩).1 lam)`. Establish `h01` using `h.2.2.1 0 1 mu mu'`. Establish `h0 : (0 : Fin 2).val = 0` using `rfl`. Establish `h1 : ¬ (1 : Fin 2).val = 0` using `by decide`.

Simplify using `only [h0, h1, ↓reduceIte] at h01`. Conclude with `h01`.
-/
private theorem eeN_mul_comm_of_val_le {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (j : ZMod J)
    (a b : Fin (Dt.nL j + r + 1)) (hab : a.val ≤ b.val) (mu mu' : Fin K → ℤ) :
    eeN D K Dt ⟨j, a⟩ mu * eeN D K Dt ⟨j, b⟩ mu' = eeN D K Dt ⟨j, b⟩ mu' * eeN D K Dt ⟨j, a⟩ mu := by
  have hmono : Monotone (fun k : Fin 2 => if k.val = 0 then NSet (r := r) Dt.nL j a.val else NSet Dt.nL j b.val) := by
    intro x y hxy
    have hxy' : x.val ≤ y.val := hxy
    dsimp only
    split_ifs <;> first | exact le_refl _ | exact NSet_mono Dt.nL j hab | omega
  have h := ((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 2 _ hmono).2
    (fun k => if k.val = 0 then eeN D K Dt ⟨j, a⟩ else eeN D K Dt ⟨j, b⟩) (by
      intro k lam
      by_cases hk : k.val = 0
      · simp only [hk, ↓reduceIte]
        exact (eeN_spec D K Dt ⟨j, a⟩).1 lam
      · simp only [hk, ↓reduceIte]
        exact (eeN_spec D K Dt ⟨j, b⟩).1 lam)
  have h01 := h.2.2.1 0 1 mu mu'
  have h0 : (0 : Fin 2).val = 0 := rfl
  have h1 : ¬ (1 : Fin 2).val = 0 := by decide
  simp only [h0, h1, ↓reduceIte] at h01
  exact h01

/- English proof (translation)
Establish `hc` using `((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1 (fun _ => NSet (r := r) Dt.nL j a.val) monotone_const).2 (fun _ => eeN D K Dt ⟨j, a⟩) (fun _ lam => (eeN_spec D K Dt ⟨j, a⟩).1 lam)`. Establish `hdisj : Disjoint (NSet (r` using `r) Dt.nL j a.val) (NSet Dt.nL j' b.val) := NSet_disj Dt.nL hj a.val b.val`. Establish `hA : ∀ c d, eeN D K Dt ⟨j, a⟩ mu * glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val) c d = glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val) c d * eeN D K Dt ⟨j, a⟩ mu` using `hc.2.1 0 mu _ hdisj`. Establish `hpres` using `comm_pres_isoSub (E := glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val)) _ hA`. Conclude with `(comm_isoProj (E := glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val)) (eeN D K Dt ⟨j, a⟩ mu) hpres (eeN D K Dt ⟨j', b⟩) (eeN_spec D K Dt ⟨j', b⟩).1 (eeN_spec D K Dt ⟨j', b⟩).2 mu').symm`.
-/
private theorem eeN_mul_comm_of_ne_index {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) {j j' : ZMod J} (hj : j ≠ j')
    (a : Fin (Dt.nL j + r + 1)) (b : Fin (Dt.nL j' + r + 1)) (mu mu' : Fin K → ℤ) :
    eeN D K Dt ⟨j, a⟩ mu * eeN D K Dt ⟨j', b⟩ mu' = eeN D K Dt ⟨j', b⟩ mu' * eeN D K Dt ⟨j, a⟩ mu := by
  have hc := ((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1
    (fun _ => NSet (r := r) Dt.nL j a.val) monotone_const).2
    (fun _ => eeN D K Dt ⟨j, a⟩) (fun _ lam => (eeN_spec D K Dt ⟨j, a⟩).1 lam)
  have hdisj : Disjoint (NSet (r := r) Dt.nL j a.val) (NSet Dt.nL j' b.val) := NSet_disj Dt.nL hj a.val b.val
  have hA : ∀ c d, eeN D K Dt ⟨j, a⟩ mu * glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val) c d =
      glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val) c d * eeN D K Dt ⟨j, a⟩ mu :=
    hc.2.1 0 mu _ hdisj
  have hpres := comm_pres_isoSub (E := glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val)) _ hA
  exact (comm_isoProj (E := glOps (KK O) K Dt.trueLet (NSet Dt.nL j' b.val)) (eeN D K Dt ⟨j, a⟩ mu) hpres
    (eeN D K Dt ⟨j', b⟩) (eeN_spec D K Dt ⟨j', b⟩).1 (eeN_spec D K Dt ⟨j', b⟩).2 mu').symm

/- English proof (translation)
Take `⟨j, a⟩` from `i`. Take `⟨j', b⟩` from `i'`. Distinguish the cases in `hj : j = j'`. Substitute `hj` using the available equality. Break down `le_total a.val b.val with hab | hab` into its components or cases.

Conclude with `eeN_mul_comm_of_val_le D K Dt S hR j a b hab mu mu'`. Conclude with `(eeN_mul_comm_of_val_le D K Dt S hR j b a hab mu' mu).symm`. Conclude with `eeN_mul_comm_of_ne_index D K Dt S hR hj a b mu mu'`.
-/
theorem eeN_comm {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (i i' : NIdx Dt) (mu mu' : Fin K → ℤ) :
    eeN D K Dt i mu * eeN D K Dt i' mu' = eeN D K Dt i' mu' * eeN D K Dt i mu := by
  obtain ⟨j, a⟩ := i
  obtain ⟨j', b⟩ := i'
  by_cases hj : j = j'
  · subst hj
    rcases le_total a.val b.val with hab | hab
    · exact eeN_mul_comm_of_val_le D K Dt S hR j a b hab mu mu'
    · exact (eeN_mul_comm_of_val_le D K Dt S hR j b a hab mu' mu).symm
  · exact eeN_mul_comm_of_ne_index D K Dt S hR hj a b mu mu'

/- English proof (translation)
Establish `hc` using `((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1 (fun _ => NSet (r := r) Dt.nL i.1 i.2.val) monotone_const).2 (fun _ => eeN D K Dt i) (fun _ lam => (eeN_spec D K Dt i).1 lam)`. Conclude with `hc.2.2.2.1 0 mu F G`.
-/
theorem eeN_selfadj {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (i : NIdx Dt) (mu : Fin K → ℤ)
    (F G : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :
    fock (eeN D K Dt i mu F) G = fock F (eeN D K Dt i mu G) := by
  have hc := ((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1
    (fun _ => NSet (r := r) Dt.nL i.1 i.2.val) monotone_const).2
    (fun _ => eeN D K Dt i) (fun _ lam => (eeN_spec D K Dt i).1 lam)
  exact hc.2.2.2.1 0 mu F G

/- English proof (translation)
Introduce `F hF`. Take `⟨hiso, hdec⟩` from `eeN_spec D K Dt i`. Establish `sys : Formalism.MainNotions.G.Joints.DecSys (fun mu => isoSub (glOps (KK O) K Dt.trueLet (NSet Dt.nL i.1 i.2.val)) mu) (eeN D K Dt i)` using `{ id_on := fun mu x hx => (hiso mu).1 x hx zero_on := fun mu nu h x hx => (hiso mu).2 nu h x hx cover := fun x => (hdec x).elim fun T hT => ⟨T, hT.1⟩ mem := fun mu x => (hdec x).elim fun T hT => hT.2 mu }`. Conclude with `Formalism.MainNotions.G.Joints.e_mem_Pol (sys := sys) (d := d) (mu := mu) (F := F) (hF := hF)`.
-/
theorem eeN_pol (i : NIdx Dt) (mu : Fin K → ℤ) (d : TL J Dt.nL r → ℕ) :
    ∀ F ∈ Pol (KK O) K d, eeN D K Dt i mu F ∈ Pol (KK O) K d := by
  intro F hF
  obtain ⟨hiso, hdec⟩ := eeN_spec D K Dt i
  have sys : Formalism.MainNotions.G.Joints.DecSys (fun mu => isoSub (glOps (KK O) K Dt.trueLet (NSet Dt.nL i.1 i.2.val)) mu)
      (eeN D K Dt i) :=
    { id_on := fun mu x hx => (hiso mu).1 x hx
      zero_on := fun mu nu h x hx => (hiso mu).2 nu h x hx
      cover := fun x => (hdec x).elim fun T hT => ⟨T, hT.1⟩
      mem := fun mu x => (hdec x).elim fun T hT => hT.2 mu }
  exact Formalism.MainNotions.G.Joints.e_mem_Pol (sys := sys) (d := d) (mu := mu) (F := F) (hF := hF)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Introduce `F G`. Simplify using `only [List.prod_nil]`. Both sides reduce to the same expression.

Consider the case `cons A l ih`. Introduce `F G`. Establish `hA0 : A ∈ A :: l` using `List.mem_cons.mpr (Or.inl rfl)`. Establish `hA` using `hs A hA0`. Establish `ih'` using `ih (fun B hB => hs B (List.mem_cons.mpr (Or.inr hB))) (fun B hB C hC => hc B (List.mem_cons.mpr (Or.inr hB)) C (List.mem_cons.mpr (Or.inr hC)))`.

Establish `hcomm : A * l.prod = l.prod * A` using `(Commute.list_prod_right l A (fun B hB => hc A hA0 B (List.mem_cons.mpr (Or.inr hB)))).eq`. Rewrite using `[List.prod_cons]`. Use `show fock (A (l.prod F)) G = fock F ((A * l.prod) G)`. Apply the tactic sequence `rw [hA, ih', hcomm] <;> rfl`.
-/
private theorem fock_list_prod_symm_of_symm_of_comm {σ R : Type*} [CommRing R] (l : List (Module.End R (MvPolynomial σ R)))
    (hs : ∀ A ∈ l, ∀ F G, fock (A F) G = fock F (A G)) (hc : ∀ A ∈ l, ∀ B ∈ l, A * B = B * A) :
    ∀ F G, fock (l.prod F) G = fock F (l.prod G) := by
  induction l with
  | nil =>
    intro F G
    simp only [List.prod_nil]
    rfl
  | cons A l ih =>
    intro F G
    have hA0 : A ∈ A :: l := List.mem_cons.mpr (Or.inl rfl)
    have hA := hs A hA0
    have ih' := ih (fun B hB => hs B (List.mem_cons.mpr (Or.inr hB)))
      (fun B hB C hC => hc B (List.mem_cons.mpr (Or.inr hB)) C (List.mem_cons.mpr (Or.inr hC)))
    have hcomm : A * l.prod = l.prod * A :=
      (Commute.list_prod_right l A (fun B hB => hc A hA0 B (List.mem_cons.mpr (Or.inr hB)))).eq
    rw [List.prod_cons]
    show fock (A (l.prod F)) G = fock F ((A * l.prod) G)
    rw [hA, ih', hcomm] <;> rfl

/- English proof (translation)
Establish `hcomm : ∀ i i' mu mu', eeN D K Dt i mu * eeN D K Dt i' mu' = eeN D K Dt i' mu' * eeN D K Dt i mu` using `fun i i' mu mu' => eeN_comm D K Dt S hR i i' mu mu'`. Use `⟨jointE_isJProj (fun i mu => (eeN_spec D K Dt i).1 mu) hcomm ka, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F G`. Use `fock_list_prod_symm_of_symm_of_comm ((Finset.univ : Finset (NIdx Dt)).toList.map fun i => eeN D K Dt i (ka i)) ?_ (jointE_comm hcomm ka) F G` and prove the remaining obligations. Introduce `A hA`.

Take `⟨i, -, rfl⟩` from `List.mem_map.mp hA`. Conclude with `eeN_selfadj D K Dt S hR i (ka i)`. Introduce `d F hF`. Conclude with `jointE_pres (Pol (KK O) K d) (fun i mu F hF => eeN_pol D K Dt i mu d F hF) ka F hF`. Introduce `F i`.

Conclude with `jointE_mem hcomm (fun i G => (eeN_spec D K Dt i).2 G) ka F i`.
-/
theorem jointN_props {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (ka : NIdx Dt → Fin K → ℤ) :
    IsJProj (normE p K Dt) {ka} (jointE (eeN D K Dt) ka) ∧
    (∀ F G, fock (jointE (eeN D K Dt) ka F) G = fock F (jointE (eeN D K Dt) ka G)) ∧
    (∀ (d : TL J Dt.nL r → ℕ), ∀ F ∈ Pol (KK O) K d, jointE (eeN D K Dt) ka F ∈ Pol (KK O) K d) ∧
    ∀ F i, jointE (eeN D K Dt) ka F ∈ isoSub (normE p K Dt i) (ka i) := by
  have hcomm : ∀ i i' mu mu', eeN D K Dt i mu * eeN D K Dt i' mu' = eeN D K Dt i' mu' * eeN D K Dt i mu :=
    fun i i' mu mu' => eeN_comm D K Dt S hR i i' mu mu'
  refine ⟨jointE_isJProj (fun i mu => (eeN_spec D K Dt i).1 mu) hcomm ka, ?_, ?_, ?_⟩
  · intro F G
    refine fock_list_prod_symm_of_symm_of_comm ((Finset.univ : Finset (NIdx Dt)).toList.map fun i => eeN D K Dt i (ka i)) ?_
      (jointE_comm hcomm ka) F G
    intro A hA
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hA
    exact eeN_selfadj D K Dt S hR i (ka i)
  · intro d F hF
    exact jointE_pres (Pol (KK O) K d) (fun i mu F hF => eeN_pol D K Dt i mu d F hF) ka F hF
  · intro F i
    exact jointE_mem hcomm (fun i G => (eeN_spec D K Dt i).2 G) ka F i

def costN (dNo : TL J Dt.nL r → ℕ) (i : NIdx Dt) : ℕ :=
  N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1)

/- English proof (translation)
Establish `hc` using `((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1 (fun _ => NSet (r := r) Dt.nL i.1 i.2.val) monotone_const).2 (fun _ => eeN D K Dt i) (fun _ lam => (eeN_spec D K Dt i).1 lam)`. Establish `h5 : InBB (O` using `O) p (((p : KK O) ^ (∑ _k : Fin 1, N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1))) • (∑ t ∈ ({fun _ => mu} : Finset (Fin 1 → Fin K → ℤ)), (List.ofFn fun k => eeN D K Dt i (t k)).prod) F) := (hc.2.2.2.2 _ dNo F hF).2 hB`. Establish `e1 : (∑ t ∈ ({fun _ => mu} : Finset (Fin 1 → Fin K → ℤ)), (List.ofFn fun k => eeN D K Dt i (t k)).prod) = eeN D K Dt i mu`. Rewrite using `[Finset.sum_singleton]`. Simplify using `[List.ofFn_succ]`.

Establish `e2 : (∑ _k : Fin 1, N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1)) = costN K Dt dNo i`. Simplify using `[costN]`. Rewrite `h5` using `[e1, e2]`. Conclude with `h5`.
-/
theorem eeN_int {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (i : NIdx Dt) (mu : Fin K → ℤ)
    (dNo : TL J Dt.nL r → ℕ) (F : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (hF : F ∈ Pol (KK O) K dNo)
    (hB : InBB (O := O) p F) : InBB (O := O) p (((p : KK O) ^ costN K Dt dNo i) • eeN D K Dt i mu F) := by
  have hc := ((Formalism.MainNotions.G.GLWeightTheory.filtered_projector_corollary_field D) p n' O S hR K (TL J Dt.nL r) Dt.trueLet 1
    (fun _ => NSet (r := r) Dt.nL i.1 i.2.val) monotone_const).2
    (fun _ => eeN D K Dt i) (fun _ lam => (eeN_spec D K Dt i).1 lam)
  have h5 : InBB (O := O) p (((p : KK O) ^ (∑ _k : Fin 1, N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1))) •
      (∑ t ∈ ({fun _ => mu} : Finset (Fin 1 → Fin K → ℤ)), (List.ofFn fun k => eeN D K Dt i (t k)).prod) F) :=
    (hc.2.2.2.2 _ dNo F hF).2 hB
  have e1 : (∑ t ∈ ({fun _ => mu} : Finset (Fin 1 → Fin K → ℤ)), (List.ofFn fun k => eeN D K Dt i (t k)).prod) =
      eeN D K Dt i mu := by
    rw [Finset.sum_singleton]
    simp [List.ofFn_succ]
  have e2 : (∑ _k : Fin 1, N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1)) = costN K Dt dNo i := by
    simp [costN]
  rw [e1, e2] at h5
  exact h5

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using ⟨hF, hB⟩`. Consider the case `cons i l ih`. Take `⟨h1, h2⟩` from `ih`. Establish `e1 : ((p : KK O) ^ ((i :: l).map (costN K Dt dNo)).sum) • ((i :: l).map fun i => eeN D K Dt i (ka i)).prod F = ((p : KK O) ^ costN K Dt dNo i) • eeN D K Dt i (ka i) (((p : KK O) ^ (l.map (costN K Dt dNo)).sum) • (l.map fun i => eeN D K Dt i (ka i)).prod F)`.

Rewrite using `[List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, map_smul, smul_smul, pow_add]`. Rewrite using `[e1]`. Conclude with `⟨Submodule.smul_mem _ _ (eeN_pol D K Dt i (ka i) dNo _ h1), eeN_int D K Dt S hR i (ka i) dNo _ h1 h2⟩`.
-/
theorem jointE_int_list {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (ka : NIdx Dt → Fin K → ℤ)
    (dNo : TL J Dt.nL r → ℕ) (l : List (NIdx Dt)) (F : MvPolynomial (TL J Dt.nL r × Fin K) (KK O))
    (hF : F ∈ Pol (KK O) K dNo) (hB : InBB (O := O) p F) :
    ((p : KK O) ^ (l.map (costN K Dt dNo)).sum) • (l.map fun i => eeN D K Dt i (ka i)).prod F ∈ Pol (KK O) K dNo ∧
    InBB (O := O) p (((p : KK O) ^ (l.map (costN K Dt dNo)).sum) • (l.map fun i => eeN D K Dt i (ka i)).prod F) := by
  induction l with
  | nil => simpa using ⟨hF, hB⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : ((p : KK O) ^ ((i :: l).map (costN K Dt dNo)).sum) • ((i :: l).map fun i => eeN D K Dt i (ka i)).prod F =
        ((p : KK O) ^ costN K Dt dNo i) • eeN D K Dt i (ka i)
          (((p : KK O) ^ (l.map (costN K Dt dNo)).sum) • (l.map fun i => eeN D K Dt i (ka i)).prod F) := by
      rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, map_smul, smul_smul,
        pow_add]
    rw [e1]
    exact ⟨Submodule.smul_mem _ _ (eeN_pol D K Dt i (ka i) dNo _ h1), eeN_int D K Dt S hR i (ka i) dNo _ h1 h2⟩

/- English proof (translation)
Establish `h` using `(jointE_int_list D K Dt S hR ka dNo (Finset.univ : Finset (NIdx Dt)).toList F hF hB).2`. Establish `hs : (List.map (costN K Dt dNo) (Finset.univ : Finset (NIdx Dt)).toList).sum = ∑ i : NIdx Dt, costN K Dt dNo i` using `by first`. Consider the case `exact Finset.sum_map_toList _ _`. Consider the case `exact Finset.sum_toList _ _`. Consider the case `simp`.

Rewrite `h` using `[hs]`. Conclude with `h`.
-/
theorem jointE_int {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (ka : NIdx Dt → Fin K → ℤ)
    (dNo : TL J Dt.nL r → ℕ) (F : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (hF : F ∈ Pol (KK O) K dNo)
    (hB : InBB (O := O) p F) :
    InBB (O := O) p (((p : KK O) ^ (∑ i : NIdx Dt, costN K Dt dNo i)) • jointE (eeN D K Dt) ka F) := by
  have h := (jointE_int_list D K Dt S hR ka dNo (Finset.univ : Finset (NIdx Dt)).toList F hF hB).2
  have hs : (List.map (costN K Dt dNo) (Finset.univ : Finset (NIdx Dt)).toList).sum = ∑ i : NIdx Dt, costN K Dt dNo i := by
    first
      | exact Finset.sum_map_toList _ _
      | exact Finset.sum_toList _ _
      | simp
  rw [hs] at h
  exact h

end Inst

section VBB

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

/- English proof (translation)
Simplify using `[vK, ordW]`.
-/
theorem vK_zero' : vK (O := O) p 0 = ⊤ := by
  simp [vK, ordW]

/- English proof (translation)
Distinguish the cases in `hm : m ∈ F.support`. Unfold `vBB`. Conclude with `Finset.inf_le (f := fun m => vK (O := O) p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) hm`. Establish `h0 : F.coeff m = 0` using `by simpa using hm`. Rewrite using `[h0, vK_zero']`.

Simplify using the standard rewrite rules.
-/
theorem vBB_le_coeff (F : MvPolynomial σ (KK O)) (m : σ →₀ ℕ) :
    vBB (O := O) p F ≤ vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  by_cases hm : m ∈ F.support
  · unfold vBB
    exact Finset.inf_le (f := fun m => vK (O := O) p (F.coeff m) +
      (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) hm
  · have h0 : F.coeff m = 0 := by simpa using hm
    rw [h0, vK_zero']
    simp

/- English proof (translation)
Establish `key : ∀ m ∈ (F + G).support, min (vBB (O` using `O) p F) (vBB (O := O) p G) ≤ vK (O := O) p ((F + G).coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by`. Introduce `m _`. Establish `h1` using `vBB_le_coeff (p := p) (O := O) F m`. Establish `h2` using `vBB_le_coeff (p := p) (O := O) G m`. Establish `hv` using `Formalism.MainNotions.G.GLWeightTheory.valuation_add_ge_min p (F.coeff m) (G.coeff m)`.

Rewrite using `[MvPolynomial.coeff_add]`. Combine the equalities or inequalities in the displayed calculation. Unfold `vBB`. Conclude with `Finset.le_inf key`.
-/
theorem vBB_add (S : UniformizedDVR p O) (F G : MvPolynomial σ (KK O)) :
    min (vBB (O := O) p F) (vBB (O := O) p G) ≤ vBB (O := O) p (F + G) := by
  have key : ∀ m ∈ (F + G).support, min (vBB (O := O) p F) (vBB (O := O) p G) ≤
      vK (O := O) p ((F + G).coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    intro m _
    have h1 := vBB_le_coeff (p := p) (O := O) F m
    have h2 := vBB_le_coeff (p := p) (O := O) G m
    have hv := Formalism.MainNotions.G.GLWeightTheory.valuation_add_ge_min p (F.coeff m) (G.coeff m)
    rw [MvPolynomial.coeff_add]
    calc min (vBB (O := O) p F) (vBB (O := O) p G)
        ≤ min (vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ))
            (vK p (G.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) := min_le_min h1 h2
      _ = min (vK p (F.coeff m)) (vK p (G.coeff m)) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
          min_add_add_right _ _ _
      _ ≤ vK p (F.coeff m + G.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
          add_le_add hv le_rfl
  unfold vBB
  exact Finset.le_inf key

/- English proof (translation)
Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Simplify using `[vBB]`. Introduce `a s ha ih`. Rewrite using `[Finset.inf_insert, Finset.sum_insert ha]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem vBB_sum (S : UniformizedDVR p O) {κ : Type} (T : Finset κ) (f : κ → MvPolynomial σ (KK O)) :
    T.inf (fun i => vBB (O := O) p (f i)) ≤ vBB (O := O) p (∑ i ∈ T, f i) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · simp [vBB]
  · intro a s ha ih
    rw [Finset.inf_insert, Finset.sum_insert ha]
    calc vBB (O := O) p (f a) ⊓ s.inf (fun i => vBB (O := O) p (f i))
        ≤ vBB (O := O) p (f a) ⊓ vBB (O := O) p (∑ i ∈ s, f i) := inf_le_inf_left _ ih
      _ ≤ vBB (O := O) p (f a + ∑ i ∈ s, f i) := vBB_add S _ _

end VBB

section Greedy

variable (D : Formalism.BasicNotions.D7) {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
  [NeZero J] [NeZero r] (K : ℕ) [NeZero K] [CharZero (KK O)] (Dt : SignedChainData p O r J)

/- English proof (translation)
Take `⟨T, hT, -⟩` from `(eeN_spec D K Dt i).2 y`. Break down `T.eq_empty_or_nonempty with hE | hne` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `hy : y = 0` using `by rw [hT, hE, Finset.sum_empty]`. Apply the tactic sequence `rw [hy, map_zero] <;> exact le_rfl`.

Take `⟨mu, -, hinf⟩` from `Finset.exists_mem_eq_inf T hne (fun mu => vBB (O := O) p (eeN D K Dt i mu y))`. Use `⟨mu, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinf]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem greedy_one (S : UniformizedDVR p O) (i : NIdx Dt) (y : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :
    ∃ mu, vBB (O := O) p (eeN D K Dt i mu y) ≤ vBB (O := O) p y := by
  obtain ⟨T, hT, -⟩ := (eeN_spec D K Dt i).2 y
  rcases T.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, ?_⟩
    have hy : y = 0 := by rw [hT, hE, Finset.sum_empty]
    rw [hy, map_zero] <;> exact le_rfl
  · obtain ⟨mu, -, hinf⟩ := Finset.exists_mem_eq_inf T hne (fun mu => vBB (O := O) p (eeN D K Dt i mu y))
    refine ⟨mu, ?_⟩
    rw [← hinf]
    calc T.inf (fun mu => vBB (O := O) p (eeN D K Dt i mu y))
        ≤ vBB (O := O) p (∑ mu ∈ T, eeN D K Dt i mu y) := vBB_sum S T _
      _ = vBB (O := O) p y := by rw [← hT]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Use `⟨fun _ _ => 0, ?_⟩` and prove the remaining obligations. Simplify using `only [List.map_nil, List.prod_nil]`. Conclude with `le_rfl`.

Consider the case `cons i l ih`. Take `⟨hi, hl'⟩` from `List.nodup_cons.mp hl`. Take `⟨ka', hka'⟩` from `ih hl'`. Take `⟨mu, hmu⟩` from `greedy_one D K Dt S i ((l.map fun i => eeN D K Dt i (ka' i)).prod y)`. Use `⟨Function.update ka' i mu, ?_⟩` and prove the remaining obligations.

Establish `hmap : (l.map fun j => eeN D K Dt j (Function.update ka' i mu j)) = l.map fun j => eeN D K Dt j (ka' j)`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `j hj`. Establish `hne : j ≠ i` using `fun h => hi (h ▸ hj)`. Rewrite using `[Function.update_apply, if_neg hne]`.

Establish `hi' : Function.update ka' i mu i = mu` using `by simp`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, hmap, hi']`. Conclude with `hmu.trans hka'`.
-/
theorem greedy_list (S : UniformizedDVR p O) (l : List (NIdx Dt)) (hl : l.Nodup)
    (y : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :
    ∃ ka : NIdx Dt → Fin K → ℤ, vBB (O := O) p ((l.map fun i => eeN D K Dt i (ka i)).prod y) ≤ vBB (O := O) p y := by
  induction l with
  | nil =>
    refine ⟨fun _ _ => 0, ?_⟩
    simp only [List.map_nil, List.prod_nil]
    exact le_rfl
  | cons i l ih =>
    obtain ⟨hi, hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨ka', hka'⟩ := ih hl'
    obtain ⟨mu, hmu⟩ := greedy_one D K Dt S i ((l.map fun i => eeN D K Dt i (ka' i)).prod y)
    refine ⟨Function.update ka' i mu, ?_⟩
    have hmap : (l.map fun j => eeN D K Dt j (Function.update ka' i mu j)) = l.map fun j => eeN D K Dt j (ka' j) := by
      apply List.map_congr_left
      intro j hj
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_apply, if_neg hne]
    have hi' : Function.update ka' i mu i = mu := by simp
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hmap, hi']
    exact hmu.trans hka'

include D in

/- English proof (translation)
Take `⟨ka0, hka0⟩` from `greedy_list D K Dt S (Finset.univ : Finset (NIdx Dt)).toList (Finset.nodup_toList _) y`. Take `⟨ka, hka⟩ : ∃ ka : ZMod J → ℕ → Fin K → ℤ, ∀ i : NIdx Dt, ka i.1 i.2.val = ka0 i` from `⟨fun j u => if h : u < Dt.nL j + r + 1 then ka0 ⟨j, ⟨u, h⟩⟩ else 0, fun i => dif_pos i.2.isLt⟩`. Establish `hfun : (fun i : Σ j, Fin (Dt.nL j + r + 1) => ka i.1 i.2.val) = ka0` using `funext hka`. Take `⟨h1, h2, h3, h4⟩` from `jointN_props D K Dt S hR ka0`. Establish `hj` using `jointE_int D K Dt S hR ka0 dNo`.

Use `⟨ka, jointE (eeN D K Dt) ka0, ?_, hka0, h2, fun F hF => ⟨h3 dNo F hF, fun hB => hj F hF hB⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Conclude with `h1`. Introduce `F i`. Rewrite using `[hka i]`.

Conclude with `h4 F i`.
-/
theorem restJP {n' : ℕ} (S : UniformizedDVR p O) (hR : AdmissibleDVR p n' O) (dNo : TL J Dt.nL r → ℕ)
    (y : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :
    ∃ (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e ∧ vBB (O := O) p (e y) ≤ vBB (O := O) p y ∧
      (∀ F G, fock (e F) G = fock F (e G)) ∧
      (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
        (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ (∑ i : Σ j, Fin (Dt.nL j + r + 1),
          N0 K * Nat.log p (2 * degIn dNo (NSet Dt.nL i.1 i.2.val) + K - 1))) • e F))) ∧
      ∀ F i, e F ∈ isoSub (normE p K Dt i) (ka i.1 i.2.val) := by
  obtain ⟨ka0, hka0⟩ := greedy_list D K Dt S (Finset.univ : Finset (NIdx Dt)).toList (Finset.nodup_toList _) y
  obtain ⟨ka, hka⟩ : ∃ ka : ZMod J → ℕ → Fin K → ℤ, ∀ i : NIdx Dt, ka i.1 i.2.val = ka0 i :=
    ⟨fun j u => if h : u < Dt.nL j + r + 1 then ka0 ⟨j, ⟨u, h⟩⟩ else 0, fun i => dif_pos i.2.isLt⟩
  have hfun : (fun i : Σ j, Fin (Dt.nL j + r + 1) => ka i.1 i.2.val) = ka0 := funext hka
  obtain ⟨h1, h2, h3, h4⟩ := jointN_props D K Dt S hR ka0
  have hj := jointE_int D K Dt S hR ka0 dNo
  refine ⟨ka, jointE (eeN D K Dt) ka0, ?_, hka0, h2, fun F hF => ⟨h3 dNo F hF, fun hB => hj F hF hB⟩, ?_⟩
  · rw [hfun]
    exact h1
  · intro F i
    rw [hka i]
    exact h4 F i

end Greedy

end Formalism.MainNotions.TestSideWords
