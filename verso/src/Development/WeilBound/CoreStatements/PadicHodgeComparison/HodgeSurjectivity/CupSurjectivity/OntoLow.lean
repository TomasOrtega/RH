import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun t _ => P.lin' N a n (φ (b t)) v (b.coord t)`.
-/
theorem ontoLow_h_basis (P : HTPre l K) (N : Model l K) (a n : ℕ) (v : N.V n) {m : ℕ}
    (b : Module.Basis (Fin m) K (Hdg N.q a n)) (φ : Module.Dual K (Hdg N.q a n)) :
    P.h N a n v φ = ∑ t, kC K (φ (b t)) * P.h N a n v (b.coord t) := by
  conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]
  rw [map_sum]
  exact Finset.sum_congr rfl fun t _ => P.lin' N a n (φ (b t)) v (b.coord t)

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]`. Rewrite using `[hsp, Category.comp_id]`. Simplify using `only [Model.genMap, Category.assoc, pullback.lift_snd, Category.id_comp]`.
-/
theorem ontoLow_genMap_comp (M N : Model l K) (p : N.X ⟶ M.X) (s : M.X ⟶ N.X) (hp : p ≫ M.p = N.p)
    (hs : s ≫ N.p = M.p) (hsp : s ≫ p = 𝟙 _) : Model.genMap s hs ≫ Model.genMap p hp = 𝟙 M.gen := by
  apply pullback.hom_ext
  · simp only [Model.genMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    rw [hsp, Category.comp_id]
  · simp only [Model.genMap, Category.assoc, pullback.lift_snd, Category.id_comp]

/- English proof (translation)
Introduce `hcup hret hon l _ K _ P hinj M d hM hd n`. Take `⟨N, p, s, hp, hsp, hN, hNd⟩` from `hret l K M d hM hd`. Establish `hs : s ≫ N.p = M.p` using `by rw [← hp, ← Category.assoc, hsp, Category.id_comp]`. Establish `hSN : Surj P N n` using `hon l K P N (d + 1) (by omega) hN hNd (hinj N hN _) n`. Introduce `m b z hz a ha`.

Establish `: ∀ a, FiniteDimensional K (Hdg N.q a n)` using `fun a => (P.fin N hN a n).1`. Set `b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg N.q a n))) K (Hdg N.q a n)` to `fun a => Module.finBasis K _`. Set `S : ∀ a, Hdg N.q a n →ₗ[K] Hdg M.q a n` to `fun a => pullH (Model.genMap s hs) (Model.genMap_q s hs) a n`. Set `z' : ∀ a, Fin (Module.finrank K (Hdg N.q a n)) → ℂ_[l]` to `fun a t => ∑ s', z a s' * kC K ((b a).coord s' (S a (b' a t)))`. Establish `hz' : ∀ a ≤ n, z' a = 0` using `hSN b' z' (by`.

Introduce `v`. Use `Eq.trans ?_ (hz (Model.pullV s hs n v))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [z', Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun s' _ => ?_` and prove the remaining obligations. Rewrite using `[P.nat M N s hs hM hN, ontoLow_h_basis P N a n v (b' a), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, S]`. Use the proof step `ring)`.

Establish `key : ∀ x, ∑ s', z a s' * kC K ((b a).coord s' (S a x)) = 0`. Introduce `x`. Rewrite using `[← (b' a).sum_repr x]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Establish `h0` using `congrFun (hz' a ha) t`. Simplify using `only [z', Pi.zero_apply] at h0`. Establish `e : ∀ s', z a s' * (kC K ((b' a).repr x t) * kC K ((b a).coord s' (S a (b' a t)))) = kC K ((b' a).repr x t) * (z a s' * kC K ((b a).coord s' (S a (b' a t))))` using `fun _ => by ring`. Repeatedly rewrite using `[e, ← Finset.mul_sum, h0, mul_zero]`.

Establish `hsurj : ∀ y, S a (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n y) = y`. Introduce `y`. Establish `h1` using `(hcup K M.gen M.q).2.2.2.2.2.2 N.gen M.gen N.q M.q (Model.genMap p hp) (Model.genMap_q p hp) (Model.genMap s hs) (Model.genMap_q s hs) (𝟙 M.gen) (Category.id_comp M.q) (ontoLow_genMap_comp M N p s hp hs hsp) a n y`. Rewrite `h1` using `[(hcup K M.gen M.q).2.2.2.2.2.1 a n y]`. Conclude with `h1`.

Use function extensionality and compare the values at `s₀`. Use `key (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n ((b a) s₀))` as an intermediate fact. Rewrite `this` using `[hsurj]`. Simplify `this` using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem ontoLow_pf : OntoLow := by
  intro hcup hret hon l _ K _ P hinj M d hM hd n
  obtain ⟨N, p, s, hp, hsp, hN, hNd⟩ := hret l K M d hM hd
  have hs : s ≫ N.p = M.p := by rw [← hp, ← Category.assoc, hsp, Category.id_comp]
  have hSN : Surj P N n := hon l K P N (d + 1) (by omega) hN hNd (hinj N hN _) n
  intro m b z hz a ha
  have : ∀ a, FiniteDimensional K (Hdg N.q a n) := fun a => (P.fin N hN a n).1
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg N.q a n))) K (Hdg N.q a n) := fun a => Module.finBasis K _
  let S : ∀ a, Hdg N.q a n →ₗ[K] Hdg M.q a n := fun a => pullH (Model.genMap s hs) (Model.genMap_q s hs) a n
  let z' : ∀ a, Fin (Module.finrank K (Hdg N.q a n)) → ℂ_[l] :=
    fun a t => ∑ s', z a s' * kC K ((b a).coord s' (S a (b' a t)))
  have hz' : ∀ a ≤ n, z' a = 0 := hSN b' z' (by
    intro v
    refine Eq.trans ?_ (hz (Model.pullV s hs n v))
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [z', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [P.nat M N s hs hM hN, ontoLow_h_basis P N a n v (b' a), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [LinearMap.comp_apply, S]
    ring)
  have key : ∀ x, ∑ s', z a s' * kC K ((b a).coord s' (S a x)) = 0 := by
    intro x
    rw [← (b' a).sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    have h0 := congrFun (hz' a ha) t
    simp only [z', Pi.zero_apply] at h0
    have e : ∀ s', z a s' * (kC K ((b' a).repr x t) * kC K ((b a).coord s' (S a (b' a t)))) =
        kC K ((b' a).repr x t) * (z a s' * kC K ((b a).coord s' (S a (b' a t)))) := fun _ => by ring
    simp_rw [e, ← Finset.mul_sum, h0, mul_zero]
  have hsurj : ∀ y, S a (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n y) = y := by
    intro y
    have h1 := (hcup K M.gen M.q).2.2.2.2.2.2 N.gen M.gen N.q M.q (Model.genMap p hp) (Model.genMap_q p hp)
      (Model.genMap s hs) (Model.genMap_q s hs) (𝟙 M.gen) (Category.id_comp M.q)
      (ontoLow_genMap_comp M N p s hp hs hsp) a n y
    rw [(hcup K M.gen M.q).2.2.2.2.2.1 a n y] at h1
    exact h1
  funext s₀
  have := key (pullH (Model.genMap p hp) (Model.genMap_q p hp) a n ((b a) s₀))
  rw [hsurj] at this
  simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using this

end CrystallineSemistableComparison.Onto

end
