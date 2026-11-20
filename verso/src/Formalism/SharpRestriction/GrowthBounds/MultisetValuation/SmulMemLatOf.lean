import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IsLatticeBetween

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Cnt

open Formalism.MainNotions.G

variable {W Qq F : Type} [CommRing W] [Field Qq] [Algebra W Qq] [Field F] [Algebra W F] {n : ℕ}

def red (F : Type) [Field F] [Algebra W F] (n : ℕ) : (Fin n → W) →ₗ[W] (Fin n → F) :=
  (Algebra.linearMap W F).compLeft (Fin n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem red_apply (w : Fin n → W) (i : Fin n) : red F n w i = algebraMap W F (w i) := rfl

structure Res (π : W) (F : Type) [Field F] [Algebra W F] : Prop where
  surj : Function.Surjective (algebraMap W F)
  ker : ∀ w, algebraMap W F w = 0 ↔ π ∣ w
  ne : π ≠ 0

variable {π : W}

/- English proof (translation)
Introduce `y`. Use `choose w hw using fun i => h.surj (y i)`. Conclude with `⟨w, funext hw⟩`.
-/
theorem red_surj (h : Res π F) : Function.Surjective (red (W := W) F n) := by
  intro y
  choose w hw using fun i => h.surj (y i)
  exact ⟨w, funext hw⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `: ∀ i, π ∣ w i` using `fun i => (h.ker _).1 (congrFun h0 i)`. Use `choose w' hw' using this`. Conclude with `⟨w', funext hw'⟩`.

Introduce and unpack `⟨w', rfl⟩`. Use function extensionality and compare the values at `i`. Rewrite using `[red_apply]`. Conclude with `(h.ker _).2 ⟨w' i, rfl⟩`.
-/
theorem red_eq_zero (h : Res π F) (w : Fin n → W) : red F n w = 0 ↔ ∃ w' : Fin n → W, w = π • w' := by
  constructor
  · intro h0
    have : ∀ i, π ∣ w i := fun i => (h.ker _).1 (congrFun h0 i)
    choose w' hw' using this
    exact ⟨w', funext hw'⟩
  · rintro ⟨w', rfl⟩
    funext i
    rw [red_apply]
    exact (h.ker _).2 ⟨w' i, rfl⟩

def toF (h : Res π F) (T : Submodule W (Fin n → F)) : Submodule F (Fin n → F) where
  carrier := T
  add_mem' := T.add_mem
  zero_mem' := T.zero_mem
  smul_mem' := by
    intro c x hx
    obtain ⟨w, rfl⟩ := h.surj c
    rw [algebraMap_smul]
    exact T.smul_mem w hx

def LatOf (g : Matrix (Fin n) (Fin n) Qq) (U : Submodule F (Fin n → F)) : Submodule W (Fin n → Qq) :=
  (Submodule.comap (red F n) (U.restrictScalars W)).map (psi g)

variable [IsDomain W] [IsPrincipalIdealRing W] [IsFractionRing W Qq]

/- English proof (translation)
Unfold `LatOf`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w', hw', he⟩`. Rewrite using `[← psi_inj (IsFractionRing.injective W Qq) g hg he]`.

Conclude with `hw'`. Introduce `hw`. Conclude with `⟨w, hw, rfl⟩`.
-/
theorem psi_mem_LatOf (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (U : Submodule F (Fin n → F))
    (w : Fin n → W) : psi g w ∈ LatOf (W := W) g U ↔ red F n w ∈ U := by
  unfold LatOf
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w', hw', he⟩
    rw [← psi_inj (IsFractionRing.injective W Qq) g hg he]
    exact hw'
  · intro hw
    exact ⟨w, hw, rfl⟩

/- English proof (translation)
Rewrite using `[← range_psi]`. Conclude with `LinearMap.map_le_range`.
-/
theorem LatOf_le (g : Matrix (Fin n) (Fin n) Qq) (U : Submodule F (Fin n → F)) : LatOf (W := W) g U ≤ colSpan W g := by
  rw [← range_psi]
  exact LinearMap.map_le_range

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[← range_psi]`. Take `⟨w, rfl⟩` from `hy`. Rewrite using `[← map_smul, psi_mem_LatOf (W := W) g hg, (red_eq_zero h _).2 ⟨w, rfl⟩]`. Conclude with `U.zero_mem`.
-/
theorem smul_mem_LatOf (h : Res π F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    (U : Submodule F (Fin n → F)) : ∀ y ∈ colSpan W g, π • y ∈ LatOf (W := W) g U := by
  intro y hy
  rw [← range_psi] at hy
  obtain ⟨w, rfl⟩ := hy
  rw [← map_smul, psi_mem_LatOf (W := W) g hg, (red_eq_zero h _).2 ⟨w, rfl⟩]
  exact U.zero_mem

/- English proof (translation)
The claim follows from `isLattice_between π h.ne g hg _ (LatOf_le g U) (smul_mem_LatOf h g hg U)`.
-/
theorem LatOf_lattice (h : Res π F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    (U : Submodule F (Fin n → F)) : IsLattice W (LatOf (W := W) g U) :=
  isLattice_between π h.ne g hg _ (LatOf_le g U) (smul_mem_LatOf h g hg U)

/- English proof (translation)
Use extensionality with `z`. Take `⟨w, rfl⟩` from `red_surj h z`. Rewrite using `[← psi_mem_LatOf (W := W) g hg, ← psi_mem_LatOf (W := W) g hg, he]`.
-/
theorem LatOf_inj (h : Res π F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    {U U' : Submodule F (Fin n → F)} (he : LatOf (W := W) g U = LatOf (W := W) g U') : U = U' := by
  ext z
  obtain ⟨w, rfl⟩ := red_surj h z
  rw [← psi_mem_LatOf (W := W) g hg, ← psi_mem_LatOf (W := W) g hg, he]

/- English proof (translation)
Use `⟨toF h ((S.comap (psi g)).map (red F n)), ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Establish `hy'` using `LatOf_le g _ hy`. Rewrite `hy'` using `[← range_psi]`.

Take `⟨w, rfl⟩` from `hy'`. Rewrite `hy` using `[psi_mem_LatOf (W := W) g hg]`. Take `⟨w', hw', he⟩` from `Submodule.mem_map.1 (show red F n w ∈ (S.comap (psi g)).map (red F n) from hy)`. Establish `h0 : red F n (w - w') = 0` using `by rw [map_sub, he, sub_self]`. Take `⟨w'', hw''⟩` from `(red_eq_zero h _).1 h0`.

Establish `: psi g w = psi g w' + π • psi g w''`. Rewrite using `[← map_smul, ← hw'', ← map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `S.add_mem hw' (h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _))`. Introduce `y hy`. Establish `hy'` using `h1 hy`. Rewrite `hy'` using `[← range_psi]`. Take `⟨w, rfl⟩` from `hy'`.

Rewrite using `[psi_mem_LatOf (W := W) g hg]`. Conclude with `Submodule.mem_map.2 ⟨w, hy, rfl⟩`.
-/
theorem LatOf_surj (h : Res π F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det)
    (S : Submodule W (Fin n → Qq)) (h1 : S ≤ colSpan W g) (h2 : ∀ y ∈ colSpan W g, π • y ∈ S) :
    ∃ U : Submodule F (Fin n → F), LatOf (W := W) g U = S := by
  refine ⟨toF h ((S.comap (psi g)).map (red F n)), ?_⟩
  apply le_antisymm
  · intro y hy
    have hy' := LatOf_le g _ hy
    rw [← range_psi] at hy'
    obtain ⟨w, rfl⟩ := hy'
    rw [psi_mem_LatOf (W := W) g hg] at hy
    obtain ⟨w', hw', he⟩ := Submodule.mem_map.1 (show red F n w ∈ (S.comap (psi g)).map (red F n) from hy)
    have h0 : red F n (w - w') = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨w'', hw''⟩ := (red_eq_zero h _).1 h0
    have : psi g w = psi g w' + π • psi g w'' := by
      rw [← map_smul, ← hw'', ← map_add]
      congr 1
      abel
    rw [this]
    exact S.add_mem hw' (h2 _ (by rw [← range_psi]; exact LinearMap.mem_range_self _ _))
  · intro y hy
    have hy' := h1 hy
    rw [← range_psi] at hy'
    obtain ⟨w, rfl⟩ := hy'
    rw [psi_mem_LatOf (W := W) g hg]
    exact Submodule.mem_map.2 ⟨w, hy, rfl⟩

/- English proof (translation)
Rewrite using `[← Module.natCard_eq_pow_finrank, ← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv W U).toEquiv]`. Apply `card_quot (colSpan W g) (LatOf (W := W) g U) (psi g) (range_psi g) ((U.restrictScalars W).mkQ.comp (red F n))` to reduce the goal to its premises. Conclude with `(Submodule.mkQ_surjective _).comp (red_surj h)`. Introduce `w`. Rewrite using `[psi_mem_LatOf (W := W) g hg, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Both sides reduce to the same expression.
-/
theorem card_down (h : Res π F) (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (U : Submodule F (Fin n → F)) :
    Nat.card (↥(colSpan W g) ⧸ Submodule.comap (colSpan W g).subtype (LatOf (W := W) g U)) =
      Nat.card F ^ Module.finrank F ((Fin n → F) ⧸ U) := by
  rw [← Module.natCard_eq_pow_finrank, ← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv W U).toEquiv]
  apply card_quot (colSpan W g) (LatOf (W := W) g U) (psi g) (range_psi g) ((U.restrictScalars W).mkQ.comp (red F n))
  · exact (Submodule.mkQ_surjective _).comp (red_surj h)
  · intro w
    rw [psi_mem_LatOf (W := W) g hg, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl

/- English proof (translation)
Establish `hsum` using `Submodule.finrank_quotient_add_finrank U`. Rewrite `hsum` using `[Module.finrank_fin_fun]`. Establish `hc` using `card_down h g hg U`. Rewrite `hc` using `[hq]`. Prove the components needed by the constructor for the conclusion.

Introduce `hE`. Establish `h5` using `hE.2.2.2.2`. Rewrite `h5` using `[hc, pow_mul]`. Use `Nat.pow_right_injective hq1 h5` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `hi`. Use `⟨LatOf_lattice h g hg U, ⟨g, hg, rfl⟩, LatOf_le g U, smul_mem_LatOf h g hg U, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, pow_mul]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem edge_down_iff (p n' i : ℕ) (h : Res (p : W) F) (hq : Nat.card F = p ^ n') (hq1 : 2 ≤ p ^ n')
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (U : Submodule F (Fin n → F)) :
    IsEdge p n' i ⟨LatOf (W := W) g U, colSpan W g⟩ ↔ Module.finrank F U + i = n := by
  have hsum := Submodule.finrank_quotient_add_finrank U
  rw [Module.finrank_fin_fun] at hsum
  have hc := card_down h g hg U
  rw [hq] at hc
  constructor
  · intro hE
    have h5 := hE.2.2.2.2
    rw [hc, pow_mul] at h5
    have := Nat.pow_right_injective hq1 h5
    omega
  · intro hi
    refine ⟨LatOf_lattice h g hg U, ⟨g, hg, rfl⟩, LatOf_le g U, smul_mem_LatOf h g hg U, ?_⟩
    rw [hc, pow_mul]
    congr 1
    omega

/- English proof (translation)
Use `symm`. Apply `Nat.card_eq_of_bijective (fun U : {U : Submodule F (Fin n → F) // Pu U ∧ Module.finrank F U + i = n} => (⟨LatOf (W := W) g U.1, (edge_down_iff p n' i h hq hq1 g hg U.1).2 U.2.2, (hP U.1).2 U.2.1⟩ : {B1 : Submodule W (Fin n → Qq) // IsEdge p n' i ⟨B1, colSpan W g⟩ ∧ Pd B1}))` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `U U' he`. Conclude with `Subtype.ext (LatOf_inj h g hg (congrArg Subtype.val he))`.

Introduce and unpack `⟨B1, hE, hPd⟩`. Take `⟨U, rfl⟩` from `LatOf_surj h g hg B1 hE.2.2.1 hE.2.2.2.1`. Conclude with `⟨⟨U, (hP U).1 hPd, (edge_down_iff p n' i h hq hq1 g hg U).1 hE⟩, rfl⟩`.
-/
theorem down_card (p n' i : ℕ) (h : Res (p : W) F) (hq : Nat.card F = p ^ n') (hq1 : 2 ≤ p ^ n')
    (g : Matrix (Fin n) (Fin n) Qq) (hg : IsUnit g.det) (Pd : Submodule W (Fin n → Qq) → Prop)
    (Pu : Submodule F (Fin n → F) → Prop) (hP : ∀ U, Pd (LatOf (W := W) g U) ↔ Pu U) :
    Nat.card {B1 : Submodule W (Fin n → Qq) // IsEdge p n' i ⟨B1, colSpan W g⟩ ∧ Pd B1} =
      Nat.card {U : Submodule F (Fin n → F) // Pu U ∧ Module.finrank F U + i = n} := by
  symm
  apply Nat.card_eq_of_bijective
    (fun U : {U : Submodule F (Fin n → F) // Pu U ∧ Module.finrank F U + i = n} =>
      (⟨LatOf (W := W) g U.1, (edge_down_iff p n' i h hq hq1 g hg U.1).2 U.2.2, (hP U.1).2 U.2.1⟩ :
        {B1 : Submodule W (Fin n → Qq) // IsEdge p n' i ⟨B1, colSpan W g⟩ ∧ Pd B1}))
  constructor
  · intro U U' he
    exact Subtype.ext (LatOf_inj h g hg (congrArg Subtype.val he))
  · rintro ⟨B1, hE, hPd⟩
    obtain ⟨U, rfl⟩ := LatOf_surj h g hg B1 hE.2.2.1 hE.2.2.2.1
    exact ⟨⟨U, (hP U).1 hPd, (edge_down_iff p n' i h hq hq1 g hg U).1 hE⟩, rfl⟩

end Formalism.MainNotions.FormalGroupSystem.Pf.Cnt
