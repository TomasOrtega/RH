import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

/- English proof (translation)
Rewrite using `[algebraMap_smul]`.
-/
theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

/- English proof (translation)
Rewrite using `[smulO_eq (A := A)]`. Conclude with `W.N.smul_mem _ hx`.
-/
theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

/- English proof (translation)
The claim follows from `W.N.smul_mem _ hn`.
-/
theorem qInv_of_mem {n : D} (hn : n ∈ W.N) : W.QInv n := W.N.smul_mem _ hn

/- English proof (translation)
Simplify using `only [QInv, smul_zero]`. Conclude with `W.N.zero_mem`.
-/
theorem qInv_zero : W.QInv 0 := by
  simp only [QInv, smul_zero]; exact W.N.zero_mem

/- English proof (translation)
Simplify using `only [QInv, smul_add]`. Conclude with `W.N.add_mem hy hy'`.
-/
theorem qInv_add {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y + y') := by
  simp only [QInv, smul_add]; exact W.N.add_mem hy hy'

/- English proof (translation)
Simplify using `only [QInv, smul_sub]`. Conclude with `W.N.sub_mem hy hy'`.
-/
theorem qInv_sub {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y - y') := by
  simp only [QInv, smul_sub]; exact W.N.sub_mem hy hy'

/- English proof (translation)
Simplify using `only [QInv]`. Rewrite using `[smul_comm]`. Conclude with `W.N.smul_mem a hy`.
-/
theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

/- English proof (translation)
Rewrite using `[smulO_eq (A := A)]`. Conclude with `W.qInv_smul _ hy`.
-/
theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy

/- English proof (translation)
Take `⟨n, hn, rfl⟩` from `hz`. Conclude with `W.N.smul_mem _ hn`.
-/
theorem xN_mem {z : D} (hz : W.XN z) : z ∈ W.N := by
  obtain ⟨n, hn, rfl⟩ := hz; exact W.N.smul_mem _ hn

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, W.N.zero_mem, (smul_zero _).symm⟩`.
-/
theorem xN_zero : W.XN 0 := ⟨0, W.N.zero_mem, (smul_zero _).symm⟩

/- English proof (translation)
Take `⟨n, hn, rfl⟩` from `hz`. Take `⟨n', hn', rfl⟩` from `hz'`. Conclude with `⟨n + n', W.N.add_mem hn hn', (smul_add _ _ _).symm⟩`.
-/
theorem xN_add {z z' : D} (hz : W.XN z) (hz' : W.XN z') : W.XN (z + z') := by
  obtain ⟨n, hn, rfl⟩ := hz; obtain ⟨n', hn', rfl⟩ := hz'
  exact ⟨n + n', W.N.add_mem hn hn', (smul_add _ _ _).symm⟩

/- English proof (translation)
Take `⟨n, hn, rfl⟩` from `hz`. Conclude with `⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩`.
-/
theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

/- English proof (translation)
Rewrite using `[smulO_eq (A := A)]`. Conclude with `W.xN_smul _ hz`.
-/
theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.qInv_zero, W.xN_zero⟩`.
-/
theorem cont_pow_X_pow_eq_zero_of_lt : W.C1 0 0 := ⟨W.qInv_zero, W.xN_zero⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.qInv_add h.1 h'.1, W.xN_add h.2 h'.2⟩`.
-/
theorem isOneCochain_add {y z y' z' : D} (h : W.C1 y z) (h' : W.C1 y' z') : W.C1 (y + y') (z + z') :=
  ⟨W.qInv_add h.1 h'.1, W.xN_add h.2 h'.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩`.
-/
theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, W.qInv_zero, (smul_zero _).symm⟩`.
-/
theorem cont_X_pow_pow_eq_zero_of_gt : W.C2 0 := ⟨0, W.qInv_zero, (smul_zero _).symm⟩

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Take `⟨y', hy', rfl⟩` from `h'`. Conclude with `⟨y + y', W.qInv_add hy hy', (smul_add _ _ _).symm⟩`.
-/
theorem isTwoCochain_add {ω ω' : D} (h : W.C2 ω) (h' : W.C2 ω') : W.C2 (ω + ω') := by
  obtain ⟨y, hy, rfl⟩ := h; obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y + y', W.qInv_add hy hy', (smul_add _ _ _).symm⟩

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `h`. Conclude with `⟨a • y, W.qInv_smul a hy, smul_comm _ _ _⟩`.
-/
theorem isTwoCochain_smul (a : A) {ω : D} (h : W.C2 ω) : W.C2 (a • ω) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨a • y, W.qInv_smul a hy, smul_comm _ _ _⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem d1_apply (y z : D) : W.d1 y z = (W.γ y - y) - (W.φ z - z) := rfl

/- English proof (translation)
Simplify using `[d1]`.
-/
theorem diffOne_zero : W.d1 0 0 = 0 := by simp [d1]

/- English proof (translation)
Simplify using `only [d1, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem diffOne_add (y z y' z' : D) : W.d1 (y + y') (z + z') = W.d1 y z + W.d1 y' z' := by
  simp only [d1, map_add]; abel

/- English proof (translation)
Simplify using `only [d1, map_smul, smul_sub]`.
-/
theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

/- English proof (translation)
Simplify using `only [d1, map_sub, W.comm]`. Normalize the expressions using the abelian group laws.
-/
theorem diffOne_diffZero (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  simp only [d1, map_sub, W.comm]; abel

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [QInv, smul_sub]`. Conclude with `W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)`. Take `⟨x', hx', h⟩` from `W.γ_N x hx`. Conclude with `⟨x', hx', h⟩`.
-/
theorem isOneCochain_diffZero {x : D} (hx : x ∈ W.N) : W.C1 (W.φ x - x) (W.γ x - x) := by
  refine ⟨?_, ?_⟩
  · simp only [QInv, smul_sub]
    exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)
  · obtain ⟨x', hx', h⟩ := W.γ_N x hx
    exact ⟨x', hx', h⟩

/- English proof (translation)
Take `⟨hy, n, hn, rfl⟩` from `h`. Take `⟨y', hy', hγ⟩` from `W.γ_QN y hy`. Take `⟨v, hv⟩` from `B.φX`. Use `⟨y' - (v • W.φ n - n), ?_, ?_⟩` and prove the remaining obligations. Use `W.qInv_sub hy' (W.qInv_sub ?_ (W.qInv_of_mem hn))` and prove the remaining obligations.

Use `W.qInv_smul v ?_` and prove the remaining obligations. Conclude with `W.φ_N n hn`. Rewrite using `[d1, hγ, W.φ_smul, hv, mul_smul, smul_sub, smul_sub]`.
-/
theorem isTwoCochain_diffOne {y z : D} (h : W.C1 y z) : W.C2 (W.d1 y z) := by
  obtain ⟨hy, n, hn, rfl⟩ := h
  obtain ⟨y', hy', hγ⟩ := W.γ_QN y hy
  obtain ⟨v, hv⟩ := B.φX
  refine ⟨y' - (v • W.φ n - n), ?_, ?_⟩
  · refine W.qInv_sub hy' (W.qInv_sub ?_ (W.qInv_of_mem hn))
    refine W.qInv_smul v ?_
    exact W.φ_N n hn
  · rw [d1, hγ, W.φ_smul, hv, mul_smul, smul_sub, smul_sub]

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.isOneCochain_diffZero hx, W.diffOne_diffZero x⟩`.
-/
theorem isOneCocycle_diffZero {x : D} (hx : x ∈ W.N) : W.Cocycle (W.φ x - x) (W.γ x - x) :=
  ⟨W.isOneCochain_diffZero hx, W.diffOne_diffZero x⟩

/- English proof (translation)
Take `⟨x, hx, rfl, rfl⟩` from `h`. Conclude with `W.isOneCocycle_diffZero hx`.
-/
theorem cocycle_of_isCob1 {y z : D} (h : W.IsCob1 y z) : W.Cocycle y z := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; exact W.isOneCocycle_diffZero hx

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero⟩`.
-/
theorem cocycle_zero : W.Cocycle 0 0 := ⟨W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.isOneCochain_add h.1 h'.1, by rw [W.diffOne_add, h.2, h'.2, add_zero]⟩`.
-/
theorem cocycle_add {y z y' z' : D} (h : W.Cocycle y z) (h' : W.Cocycle y' z') :
    W.Cocycle (y + y') (z + z') :=
  ⟨W.isOneCochain_add h.1 h'.1, by rw [W.diffOne_add, h.2, h'.2, add_zero]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩`.
-/
theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, W.N.zero_mem, by simp, by simp⟩`.
-/
theorem isCob1_zero : W.IsCob1 0 0 := ⟨0, W.N.zero_mem, by simp, by simp⟩

/- English proof (translation)
Take `⟨x, hx, rfl, rfl⟩` from `h`. Take `⟨x', hx', rfl, rfl⟩` from `h'`. Apply the tactic sequence `refine ⟨x + x', W.N.add_mem hx hx', ?_, ?_⟩ <;> simp only [map_add] <;> abel`.
-/
theorem isCob1_add {y z y' z' : D} (h : W.IsCob1 y z) (h' : W.IsCob1 y' z') :
    W.IsCob1 (y + y') (z + z') := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; obtain ⟨x', hx', rfl, rfl⟩ := h'
  refine ⟨x + x', W.N.add_mem hx hx', ?_, ?_⟩ <;> simp only [map_add] <;> abel

/- English proof (translation)
Take `⟨x, hx, rfl, rfl⟩` from `h`. Conclude with `⟨c • x, W.smulO_mem c hx, by rw [map_smul, smul_sub], by rw [map_smul, smul_sub]⟩`.
-/
theorem isCob1_smulO (c : O) {y z : D} (h : W.IsCob1 y z) : W.IsCob1 (c • y) (c • z) := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  exact ⟨c • x, W.smulO_mem c hx, by rw [map_smul, smul_sub], by rw [map_smul, smul_sub]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero.symm⟩`.
-/
theorem isCob2_zero : W.IsCob2 0 := ⟨0, 0, W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero.symm⟩

/- English proof (translation)
Take `⟨y, z, hc, rfl⟩` from `h`. Take `⟨y', z', hc', rfl⟩` from `h'`. Conclude with `⟨y + y', z + z', W.isOneCochain_add hc hc', (W.diffOne_add _ _ _ _).symm⟩`.
-/
theorem isCob2_add {ω ω' : D} (h : W.IsCob2 ω) (h' : W.IsCob2 ω') : W.IsCob2 (ω + ω') := by
  obtain ⟨y, z, hc, rfl⟩ := h; obtain ⟨y', z', hc', rfl⟩ := h'
  exact ⟨y + y', z + z', W.isOneCochain_add hc hc', (W.diffOne_add _ _ _ _).symm⟩

/- English proof (translation)
Take `⟨y, z, hc, rfl⟩` from `h`. Conclude with `⟨c • y, c • z, W.isOneCochain_smul_of_tower c hc, (W.diffOne_smul_of_tower _ _ _).symm⟩`.
-/
theorem isCob2_smulO (c : O) {ω : D} (h : W.IsCob2 ω) : W.IsCob2 (c • ω) := by
  obtain ⟨y, z, hc, rfl⟩ := h
  exact ⟨c • y, c • z, W.isOneCochain_smul_of_tower c hc, (W.diffOne_smul_of_tower _ _ _).symm⟩

def qInvSub : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' := W.qInv_add
  zero_mem' := W.qInv_zero
  smul_mem' := fun a _ hy => W.qInv_smul a hy

def xNSub : Submodule A D where
  carrier := {z | W.XN z}
  add_mem' := W.xN_add
  zero_mem' := W.xN_zero
  smul_mem' := fun a _ hz => W.xN_smul a hz

def twoCochains : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := W.isTwoCochain_add
  zero_mem' := W.cont_X_pow_pow_eq_zero_of_gt
  smul_mem' := fun a _ h => W.isTwoCochain_smul a h

def cocycleSub : Submodule O (D × D) where
  carrier := {pr | W.Cocycle pr.1 pr.2}
  add_mem' := fun h h' => W.cocycle_add h h'
  zero_mem' := W.cocycle_zero
  smul_mem' := fun c _ h => W.cocycle_smulO c h

def isCob1Sub : Submodule O (D × D) where
  carrier := {pr | W.IsCob1 pr.1 pr.2}
  add_mem' := fun h h' => W.isCob1_add h h'
  zero_mem' := W.isCob1_zero
  smul_mem' := fun c _ h => W.isCob1_smulO c h

def isCob2Sub : Submodule O D where
  carrier := {ω | W.IsCob2 ω}
  add_mem' := W.isCob2_add
  zero_mem' := W.isCob2_zero
  smul_mem' := fun c _ h => W.isCob2_smulO c h

/- English proof (translation)
Rewrite using `[Z1, LinearMap.mem_ker, LinearMap.coprod_apply]`. Simplify using `only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, d1]`. Rewrite using `[← sub_eq_add_neg]`.
-/
theorem mem_Z1_iff_cocycle (y z : D) : (y, z) ∈ W.Z1 ↔ W.d1 y z = 0 := by
  rw [Z1, LinearMap.mem_ker, LinearMap.coprod_apply]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, d1]
  rw [← sub_eq_add_neg]

/- English proof (translation)
The claim follows from `W.mem_Z1_iff_cocycle pr.1 pr.2`.
-/
theorem mem_cocycles' (pr : D × D) : pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := W.mem_Z1_iff_cocycle pr.1 pr.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, by simp [LinearMap.prod_apply]⟩`.
-/
theorem diffZero_mem_coboundaries (x : D) : (W.φ x - x, W.γ x - x) ∈ W.B1 :=
  ⟨x, by simp [LinearMap.prod_apply]⟩

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[W.mem_cocycles']`. Simplify `W.diffOne_diffZero x` using `[LinearMap.prod_apply]`.
-/
theorem coboundaries_le_cocycles : W.B1 ≤ W.Z1 := by
  rintro _ ⟨x, rfl⟩
  rw [W.mem_cocycles']
  simpa [LinearMap.prod_apply] using W.diffOne_diffZero x

/- English proof (translation)
The claim follows from `(W.mem_Z1_iff_cocycle y z).2 h.2`.
-/
theorem mem_cocycles_of_isOneCocycle {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Z1 :=
  (W.mem_Z1_iff_cocycle y z).2 h.2

/- English proof (translation)
The claim follows from `sup_le (Submodule.span_le.2 fun _ h => h.1) W.coboundaries_le_cocycles`.
-/
theorem finiteCocycles_le_cocycles : W.Zf ≤ W.Z1 :=
  sup_le (Submodule.span_le.2 fun _ h => h.1) W.coboundaries_le_cocycles

/- English proof (translation)
Use `Submodule.mem_sup_left (Submodule.subset_span ⟨W.mem_cocycles_of_isOneCocycle h, 0, 0, W.B1.zero_mem, ?_⟩)` and prove the remaining obligations. Simplify using `only [pow_zero, one_smul, add_zero]`. Conclude with `⟨⟨M, h.1.1⟩, h.1.2⟩`.
-/
theorem cocycle_mem_Zf {y z : D} (h : W.Cocycle y z) : (y, z) ∈ W.Zf := by
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨W.mem_cocycles_of_isOneCocycle h, 0, 0,
    W.B1.zero_mem, ?_⟩)
  simp only [pow_zero, one_smul, add_zero]
  exact ⟨⟨M, h.1.1⟩, h.1.2⟩

/- English proof (translation)
Take `⟨x, _, rfl, rfl⟩` from `h`. Conclude with `W.diffZero_mem_coboundaries x`.
-/
theorem mem_coboundaries_of_isOneCoboundary {y z : D} (h : W.IsCob1 y z) : (y, z) ∈ W.B1 := by
  obtain ⟨x, _, rfl, rfl⟩ := h; exact W.diffZero_mem_coboundaries x

end WachMod

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W`. Conclude with `⟨fun _ hx => W.isOneCochain_diffZero hx, W.diffOne_diffZero, fun _ _ h => W.isTwoCochain_diffOne h, fun _ _ h => W.cocycle_of_isCob1 h⟩`.
-/
theorem differentialsComplex_holds : Complex := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ hx => W.isOneCochain_diffZero hx, W.diffOne_diffZero, fun _ _ h => W.isTwoCochain_diffOne h,
    fun _ _ h => W.cocycle_of_isCob1 h⟩

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W`. Conclude with `⟨⟨W.qInvSub, fun _ => Iff.rfl⟩, ⟨W.xNSub, fun _ => Iff.rfl⟩, ⟨W.twoCochains, fun _ => Iff.rfl⟩, ⟨W.cocycleSub, fun _ _ => Iff.rfl⟩, ⟨W.isCob1Sub, fun _ _ => Iff.rfl⟩, ⟨W.isCob2Sub, fun _ => Iff.rfl⟩, fun _ hn => W.qInv_of_mem hn, fun _ h => W.xN_mem h⟩`.
-/
theorem cochainsSubmodules_holds : Submods := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨⟨W.qInvSub, fun _ => Iff.rfl⟩, ⟨W.xNSub, fun _ => Iff.rfl⟩,
    ⟨W.twoCochains, fun _ => Iff.rfl⟩, ⟨W.cocycleSub, fun _ _ => Iff.rfl⟩,
    ⟨W.isCob1Sub, fun _ _ => Iff.rfl⟩, ⟨W.isCob2Sub, fun _ => Iff.rfl⟩,
    fun _ hn => W.qInv_of_mem hn, fun _ h => W.xN_mem h⟩

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W`. Conclude with `⟨fun _ _ h => W.cocycle_mem_Zf h, W.coboundaries_le_cocycles, W.finiteCocycles_le_cocycles, fun _ _ h => W.mem_coboundaries_of_isOneCoboundary h⟩`.
-/
theorem cocyclesFinite_holds : CocZf := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ _ h => W.cocycle_mem_Zf h, W.coboundaries_le_cocycles, W.finiteCocycles_le_cocycles,
    fun _ _ h => W.mem_coboundaries_of_isOneCoboundary h⟩

end Formalism.CoboundaryTransfers
