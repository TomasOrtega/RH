import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.ScalEquivGen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S`.
-/
theorem memOrthQ {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S

/- English proof (translation)
The claim follows from `S.herm.eq_iff`.
-/
theorem hTCommQ {x y : S.V} : S.hT x y = 0 ↔ S.hT y x = 0 := S.herm.eq_iff

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[memOrthQ]`. Conclude with `fun x hx => hv x (h hx)`.
-/
theorem orthAntiQ {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := by
  intro v hv
  rw [memOrthQ] at hv ⊢
  exact fun x hx => hv x (h hx)

/- English proof (translation)
Use `symm`. Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises. Introduce `u hu`. Rewrite using `[memOrthQ]`. Introduce `x hx`.

Conclude with `hTCommQ.mp ((memOrthQ.mp hx) u hu)`. Establish `h1` using `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U`. Establish `h2` using `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)`. Use linear arithmetic over natural numbers and integers.
-/
theorem orthOrthQ (U : Submodule E S.V) : orth S (orth S U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · intro u hu
    rw [memOrthQ]
    intro x hx
    exact hTCommQ.mp ((memOrthQ.mp hx) u hu)
  · have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U
    have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)
    omega

/- English proof (translation)
Use `show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)`. Use `congr 1`. Rewrite using `[← Set.image_univ]`. Use `congr 1`. Use extensionality with `i`.

Simplify using the standard rewrite rules.
-/
theorem XflagTopQ {r : ℕ} {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i
  simp

/- English proof (translation)
Use `show F.fl.X ≤ F.fl.X ⊔ Submodule.span E {F.fl.z}`. Conclude with `le_sup_left`.
-/
theorem XspLeXplusQ {r : ℕ} {T : E} (F : LFlag S r T) : Xsp F ≤ Xplus F := by
  show F.fl.X ≤ F.fl.X ⊔ Submodule.span E {F.fl.z}
  exact le_sup_left

/- English proof (translation)
Use `show F.fl.z ∈ F.fl.X ⊔ Submodule.span E {F.fl.z}`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.
-/
theorem zMemXplusQ {r : ℕ} {T : E} (F : LFlag S r T) : F.fl.z ∈ Xplus F := by
  show F.fl.z ∈ F.fl.X ⊔ Submodule.span E {F.fl.z}
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨orthAntiQ (XspLeXplusQ F) h, memOrthQ.mp h _ (zMemXplusQ F)⟩`. Introduce and unpack `⟨h1, h2⟩`. Rewrite using `[memOrthQ]`.

Introduce `x hx`. Express the relevant statement in the definitionally equal form `x ∈ F.fl.X ⊔ Submodule.span E {F.fl.z} at hx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hb`. Establish `ha' : a ∈ Xsp F` using `ha`.

Rewrite using `[map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, smul_zero, memOrthQ.mp h1 a ha', add_zero]`.
-/
theorem memOrthXplusQ {r : ℕ} {T : E} (F : LFlag S r T) {v : S.V} :
    v ∈ orth S (Xplus F) ↔ v ∈ orth S (Xsp F) ∧ S.hT F.fl.z v = 0 := by
  constructor
  · intro h
    exact ⟨orthAntiQ (XspLeXplusQ F) h, memOrthQ.mp h _ (zMemXplusQ F)⟩
  · rintro ⟨h1, h2⟩
    rw [memOrthQ]
    intro x hx
    change x ∈ F.fl.X ⊔ Submodule.span E {F.fl.z} at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have ha' : a ∈ Xsp F := ha
    rw [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, smul_zero,
      memOrthQ.mp h1 a ha', add_zero]

section Maps

variable {r : ℕ} {T' : E} {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

/- English proof (translation)
Rewrite using `[← XflagTopQ, ← h r]`. Conclude with `Submodule.mem_map_of_mem (by rw [XflagTopQ]; exact hx)`.
-/
theorem mapXQ (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) {x : S.V}
    (hx : x ∈ Xsp F') : β x ∈ Xsp F'' := by
  rw [← XflagTopQ, ← h r]
  exact Submodule.mem_map_of_mem (by rw [XflagTopQ]; exact hx)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← h j]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨w, hw, rfl⟩, rfl⟩`. Simplify using `using hw`.

Introduce `hx`. Conclude with `Submodule.mem_map.mpr ⟨β x, Submodule.mem_map_of_mem hx, by simp⟩`.
-/
theorem XflagSymmQ (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (j : ℕ) :
    (Xflag F'' j).map (β.symm : S.V →ₗ[E] S.V) = Xflag F' j := by
  ext x
  rw [← h j]
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hx
    exact Submodule.mem_map.mpr ⟨β x, Submodule.mem_map_of_mem hx, by simp⟩

/- English proof (translation)
Use `show ∀ x y, S.hT (β.symm x) (β.symm y) = S.hT x y`. Introduce `x y`. Use `hi (β.symm x) (β.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Conclude with `this.symm`.
-/
theorem isomSymmQ (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) : β.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  show ∀ x y, S.hT (β.symm x) (β.symm y) = S.hT x y
  intro x y
  have := hi (β.symm x) (β.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

/- English proof (translation)
Use `show ∀ x y, S.hT ((β.trans γ) x) ((β.trans γ) y) = S.hT x y`. Introduce `x y`. Rewrite using `[LinearEquiv.trans_apply, LinearEquiv.trans_apply, h2 (β x) (β y), h1 x y]`.
-/
theorem isomTransQ {γ : S.V ≃ₗ[E] S.V} (h1 : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h2 : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    β.trans γ ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  show ∀ x y, S.hT ((β.trans γ) x) ((β.trans γ) y) = S.hT x y
  intro x y
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h2 (β x) (β y), h1 x y]

/- English proof (translation)
Rewrite `hx`, the goal using `[memOrthQ]`. Introduce `y hy`. Establish `h0` using `hx (β.symm y) (mapXQ (XflagSymmQ h) hy)`. Establish `e : S.hT (β (β.symm y)) (β x) = S.hT (β.symm y) x` using `hi (β.symm y) x`. Rewrite `e` using `[LinearEquiv.apply_symm_apply]`.

Rewrite using `[e]`. Conclude with `h0`.
-/
theorem mapOrthXQ (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    {x : S.V} (hx : x ∈ orth S (Xsp F')) : β x ∈ orth S (Xsp F'') := by
  rw [memOrthQ] at hx ⊢
  intro y hy
  have h0 := hx (β.symm y) (mapXQ (XflagSymmQ h) hy)
  have e : S.hT (β (β.symm y)) (β x) = S.hT (β.symm y) x := hi (β.symm y) x
  rw [LinearEquiv.apply_symm_apply] at e
  rw [e]
  exact h0

/- English proof (translation)
Rewrite `hx`, the goal using `[memOrthXplusQ]`. Use `⟨mapOrthXQ hi h hx.1, ?_⟩` and prove the remaining obligations. Establish `e : S.hT (β F'.fl.z) (β x) = S.hT F'.fl.z x` using `hi F'.fl.z x`. Rewrite using `[← hz, e]`. Conclude with `hx.2`.
-/
theorem mapOrthXplusQ (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (hz : β F'.fl.z = F''.fl.z)
    {x : S.V} (hx : x ∈ orth S (Xplus F')) : β x ∈ orth S (Xplus F'') := by
  rw [memOrthXplusQ] at hx ⊢
  refine ⟨mapOrthXQ hi h hx.1, ?_⟩
  have e : S.hT (β F'.fl.z) (β x) = S.hT F'.fl.z x := hi F'.fl.z x
  rw [← hz, e]
  exact hx.2

variable {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Establish `h2` using `h.2`. Unfold `Formalism.HermitianLatticesTheory.gmap at h2`. Rewrite using `[← h2]`. Conclude with `Submodule.mem_map_of_mem hx`.
-/
theorem fwdMemQ (h : IsAutLam S Λ β) {x : S.V} (hx : x ∈ Λ) : β x ∈ Λ := by
  have h2 := h.2
  unfold Formalism.HermitianLatticesTheory.gmap at h2
  rw [← h2]
  exact Submodule.mem_map_of_mem hx

/- English proof (translation)
Establish `h2` using `h.2`. Unfold `Formalism.HermitianLatticesTheory.gmap at h2`. Rewrite `hx` using `[← h2]`. Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`.
-/
theorem bwdMemQ (h : IsAutLam S Λ β) {x : S.V} (hx : x ∈ Λ) : β.symm x ∈ Λ := by
  have h2 := h.2
  unfold Formalism.HermitianLatticesTheory.gmap at h2
  rw [← h2] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `h1 y hy`.

Introduce `hx`. Use `Submodule.mem_map.mpr ⟨β.symm x, h2 x hx, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem gmapOfQ (h1 : ∀ x ∈ Λ, β x ∈ Λ) (h2 : ∀ x ∈ Λ, β.symm x ∈ Λ) : Formalism.HermitianLatticesTheory.gmap β Λ = Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h1 y hy
  · intro hx
    refine Submodule.mem_map.mpr ⟨β.symm x, h2 x hx, ?_⟩
    simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨isomSymmQ h.1, gmapOfQ (fun x hx => bwdMemQ h hx) (fun x hx => by simpa using fwdMemQ h hx)⟩`.
-/
theorem autSymmQ (h : IsAutLam S Λ β) : IsAutLam S Λ β.symm :=
  ⟨isomSymmQ h.1, gmapOfQ (fun x hx => bwdMemQ h hx) (fun x hx => by simpa using fwdMemQ h hx)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨isomTransQ h1.1 h2.1, gmapOfQ (fun x hx => fwdMemQ h2 (fwdMemQ h1 hx)) (fun x hx => by rw [LinearEquiv.symm_trans_apply]; exact bwdMemQ h1 (bwdMemQ h2 hx))⟩`.
-/
theorem autTransQ {γ : S.V ≃ₗ[E] S.V} (h1 : IsAutLam S Λ β) (h2 : IsAutLam S Λ γ) :
    IsAutLam S Λ (β.trans γ) :=
  ⟨isomTransQ h1.1 h2.1, gmapOfQ (fun x hx => fwdMemQ h2 (fwdMemQ h1 hx))
    (fun x hx => by rw [LinearEquiv.symm_trans_apply]; exact bwdMemQ h1 (bwdMemQ h2 hx))⟩

/- English proof (translation)
Establish `hx1 : x ∈ Λ` using `hx.1`. Establish `hx2 : x ∈ orth S (Xsp F')` using `hx.2`. Use `show β x ∈ Λ ⊓ toO S (orth S (Xsp F''))`. Conclude with `Submodule.mem_inf.mpr ⟨fwdMemQ hA hx1, mapOrthXQ hA.1 h hx2⟩`.
-/
theorem lrepMapQ (hA : IsAutLam S Λ β) (h : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    {x : S.V} (hx : x ∈ Lrep Λ F') : β x ∈ Lrep Λ F'' := by
  have hx1 : x ∈ Λ := hx.1
  have hx2 : x ∈ orth S (Xsp F') := hx.2
  show β x ∈ Λ ⊓ toO S (orth S (Xsp F''))
  exact Submodule.mem_inf.mpr ⟨fwdMemQ hA hx1, mapOrthXQ hA.1 h hx2⟩

end Maps

section Pairs

variable {Λ : Submodule (𝓞 E) S.V} {r g : ℕ} {T T' : E} {F : LFlag S r T}
  {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}

/- English proof (translation)
Introduce `x hx l hl`. Establish `h0` using `hI (β.symm x) (lrepMapQ (autSymmQ hA) (XflagSymmQ hX) hx) l hl`. Rewrite `h0` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h0.symm`.
-/
theorem iotaSymmQ (hA : IsAutLam S Λ β) (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    (hI : IotaCompat Λ F F' F'' β g) : IotaCompat Λ F F'' F' β.symm g := by
  intro x hx l hl
  have h0 := hI (β.symm x) (lrepMapQ (autSymmQ hA) (XflagSymmQ hX) hx) l hl
  rw [LinearEquiv.apply_symm_apply] at h0
  exact h0.symm

/- English proof (translation)
Introduce `x hx l hl`. Conclude with `(hI1 x hx l hl).trans (hI2 (β x) (lrepMapQ hA hX hx) l hl)`.
-/
theorem iotaTransQ (hA : IsAutLam S Λ β) (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    (hI1 : IotaCompat Λ F F' F'' β g) (hI2 : IotaCompat Λ F F'' F''' γ g) :
    IotaCompat Λ F F' F''' (β.trans γ) g := by
  intro x hx l hl
  exact (hI1 x hx l hl).trans (hI2 (β x) (lrepMapQ hA hX hx) l hl)

/- English proof (translation)
Use `⟨⟨?_, gmapOfQ (fun x hx => hx) (fun x hx => hx)⟩, fun j => by simp, rfl, ?_⟩` and prove the remaining obligations. Introduce `x y`. Both sides reduce to the same expression. Introduce `x _ l _`. Conclude with `Iff.rfl`.
-/
theorem pairReflQ : IsPair Λ F F' F' (LinearEquiv.refl E S.V) g := by
  refine ⟨⟨?_, gmapOfQ (fun x hx => hx) (fun x hx => hx)⟩, fun j => by simp, rfl, ?_⟩
  · intro x y
    rfl
  · intro x _ l _
    exact Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨autSymmQ hP.1, XflagSymmQ hP.2.1, by rw [← hP.2.2.1, LinearEquiv.symm_apply_apply], iotaSymmQ hP.1 hP.2.1 hP.2.2.2⟩`.
-/
theorem pairSymmQ (hP : IsPair Λ F F' F'' β g) : IsPair Λ F F'' F' β.symm g :=
  ⟨autSymmQ hP.1, XflagSymmQ hP.2.1, by rw [← hP.2.2.1, LinearEquiv.symm_apply_apply],
    iotaSymmQ hP.1 hP.2.1 hP.2.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨autTransQ hP1.1 hP2.1, fun j => by rw [LinearEquiv.coe_trans, Submodule.map_comp, hP1.2.1 j, hP2.2.1 j], by rw [LinearEquiv.trans_apply, hP1.2.2.1, hP2.2.2.1], iotaTransQ hP1.1 hP1.2.1 hP1.2.2.2 hP2.2.2.2⟩`.
-/
theorem pairTransQ (hP1 : IsPair Λ F F' F'' β g) (hP2 : IsPair Λ F F'' F''' γ g) :
    IsPair Λ F F' F''' (β.trans γ) g :=
  ⟨autTransQ hP1.1 hP2.1,
    fun j => by rw [LinearEquiv.coe_trans, Submodule.map_comp, hP1.2.1 j, hP2.2.1 j],
    by rw [LinearEquiv.trans_apply, hP1.2.2.1, hP2.2.2.1],
    iotaTransQ hP1.1 hP1.2.1 hP1.2.2.2 hP2.2.2.2⟩

end Pairs

section Theta

variable {Λ : Submodule (𝓞 E) S.V} {r k : ℕ} {T T' : E} {F : LFlag S r T}
  {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}

def ND (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  finrank E (UUE Λ F F') = 2 * r + 2 ∧ UUE Λ F F' ⊓ orth S (UUE Λ F F') = ⊥

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hL hL' hG`.
-/
theorem ndOfQ (hΛ : Submodule.IsLattice E Λ) (hL : IsLift Λ F) (hL' : IsLift Λ F')
    (hG : Gval F F' ≠ 0) : ND Λ F F' :=
  PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hL hL' hG

/- English proof (translation)
Establish `h0` using `PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')`. Rewrite `h0` using `[n.1]`. Use `show finrank E (orth S (UUE Λ F F')) + 1 = k`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrankHpQ (hdim : finrank E S.V = k + 2 * r + 1) (n : ND Λ F F') :
    finrank E (Hp Λ F F') + 1 = k := by
  have h0 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')
  rw [n.1] at h0
  show finrank E (orth S (UUE Λ F F')) + 1 = k
  omega

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem memThPairsQ {p : S.V × S.V} :
    p ∈ ThPairs Λ F F' F'' β ↔
      ((p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'') ∧ p.1 - p.2 ∈ Xsp F) ∧ β p.1 - p.2 ∈ Xsp F'' :=
  Iff.rfl

/- English proof (translation)
Introduce `y hy`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hy`. Conclude with `(memThPairsQ.mp hp).1.1.1`.
-/
theorem thLeQ : Th Λ F F' F'' β ≤ Hp Λ F F' := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  exact (memThPairsQ.mp hp).1.1.1

/- English proof (translation)
Introduce `y hy`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hy`. Conclude with `(memThPairsQ.mp hp).1.1.2`.
-/
theorem thLe''Q : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  exact (memThPairsQ.mp hp).1.1.2

/- English proof (translation)
Apply `Submodule.eq_of_le_of_finrank_le thLeQ` to reduce the goal to its premises. Establish `h0` using `finrankHpQ hdim n`. Simplify using `only [s0] at hs`. Use linear arithmetic over natural numbers and integers.
-/
theorem thEqQ (hdim : finrank E S.V = k + 2 * r + 1) (n : ND Λ F F') (hs : s0 Λ F F' F'' β k = 1) :
    Th Λ F F' F'' β = Hp Λ F F' := by
  apply Submodule.eq_of_le_of_finrank_le thLeQ
  have h0 := finrankHpQ hdim n
  simp only [s0] at hs
  omega

/- English proof (translation)
Establish `e` using `le_antisymm thLeQ h`. Establish `h0` using `finrankHpQ hdim n`. Simplify using `only [s0]`. Rewrite using `[e]`. Use linear arithmetic over natural numbers and integers.
-/
theorem scalar_factor_eq_one_of_le (hdim : finrank E S.V = k + 2 * r + 1) (n : ND Λ F F')
    (h : Hp Λ F F' ≤ Th Λ F F' F'' β) : s0 Λ F F' F'' β k = 1 := by
  have e := le_antisymm thLeQ h
  have h0 := finrankHpQ hdim n
  simp only [s0]
  rw [e]
  omega

/- English proof (translation)
Establish `hTh` using `thEqQ hdim n' hs`. Establish `hfst : Function.Injective ((LinearMap.fst E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype)`. Apply `LinearMap.ker_eq_bot.mp` to reduce the goal to its premises. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce and unpack `⟨p, hp⟩ h0`.

Express the relevant statement in the definitionally equal form `p.1 = 0 at h0`. Rewrite `hp` using `[memThPairsQ]`. Establish `h2 : p.2 ∈ UUE Λ F F'' ⊓ orth S (UUE Λ F F'')`. Use `Submodule.mem_inf.mpr ⟨PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F'' ?_, hp.1.1.2⟩` and prove the remaining obligations. Establish `h3` using `(Xsp F).neg_mem hp.1.2`.

Rewrite `h3` using `[h0, zero_sub, neg_neg]`. Then use the resulting hypothesis. Rewrite `h2` using `[n''.2, Submodule.mem_bot]`. Conclude with `Subtype.ext (Prod.ext h0 h2)`. Establish `hsnd : Function.Injective ((LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype)`. Apply `LinearMap.ker_eq_bot.mp` to reduce the goal to its premises.

Rewrite using `[LinearMap.ker_eq_bot']`. Introduce and unpack `⟨p, hp⟩ h0`. Express the relevant statement in the definitionally equal form `p.2 = 0 at h0`. Rewrite `hp` using `[memThPairsQ]`. Establish `h1 : p.1 ∈ UUE Λ F F' ⊓ orth S (UUE Λ F F')`.

Use `Submodule.mem_inf.mpr ⟨PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F' ?_, hp.1.1.1⟩` and prove the remaining obligations. Establish `h3` using `hp.1.2`. Rewrite `h3` using `[h0, sub_zero]`. Then use the resulting hypothesis. Rewrite `h1` using `[n'.2, Submodule.mem_bot]`. Conclude with `Subtype.ext (Prod.ext h1 h0)`.

Establish `e1 : finrank E (Th Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β)`. Establish `e : Th Λ F F' F'' β = LinearMap.range ((LinearMap.fst E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression. Rewrite using `[e, LinearMap.finrank_range_of_inj hfst]`.

Establish `e2 : finrank E (Th'' Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β)`. Establish `e : Th'' Λ F F' F'' β = LinearMap.range ((LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression. Rewrite using `[e, LinearMap.finrank_range_of_inj hsnd]`.

Apply `Submodule.eq_of_le_of_finrank_le thLe''Q` to reduce the goal to its premises. Establish `h1` using `finrankHpQ hdim n'`. Establish `h2` using `finrankHpQ hdim n''`. Rewrite `e1` using `[hTh]`. Use linear arithmetic over natural numbers and integers.
-/
theorem thEq''Q (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (n' : ND Λ F F') (n'' : ND Λ F F'') (hs : s0 Λ F F' F'' β k = 1) :
    Th'' Λ F F' F'' β = Hp Λ F F'' := by
  have hTh := thEqQ hdim n' hs
  have hfst : Function.Injective
      ((LinearMap.fst E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨p, hp⟩ h0
    change p.1 = 0 at h0
    rw [memThPairsQ] at hp
    have h2 : p.2 ∈ UUE Λ F F'' ⊓ orth S (UUE Λ F F'') := by
      refine Submodule.mem_inf.mpr ⟨PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F'' ?_, hp.1.1.2⟩
      have h3 := (Xsp F).neg_mem hp.1.2
      rwa [h0, zero_sub, neg_neg] at h3
    rw [n''.2, Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h0 h2)
  have hsnd : Function.Injective
      ((LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    rintro ⟨p, hp⟩ h0
    change p.2 = 0 at h0
    rw [memThPairsQ] at hp
    have h1 : p.1 ∈ UUE Λ F F' ⊓ orth S (UUE Λ F F') := by
      refine Submodule.mem_inf.mpr ⟨PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F' ?_, hp.1.1.1⟩
      have h3 := hp.1.2
      rwa [h0, sub_zero] at h3
    rw [n'.2, Submodule.mem_bot] at h1
    exact Subtype.ext (Prod.ext h1 h0)
  have e1 : finrank E (Th Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β) := by
    have e : Th Λ F F' F'' β =
        LinearMap.range ((LinearMap.fst E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [e, LinearMap.finrank_range_of_inj hfst]
  have e2 : finrank E (Th'' Λ F F' F'' β) = finrank E (ThPairs Λ F F' F'' β) := by
    have e : Th'' Λ F F' F'' β =
        LinearMap.range ((LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [e, LinearMap.finrank_range_of_inj hsnd]
  apply Submodule.eq_of_le_of_finrank_le thLe''Q
  have h1 := finrankHpQ hdim n'
  have h2 := finrankHpQ hdim n''
  rw [hTh] at e1
  omega

/- English proof (translation)
Rewrite using `[← orthOrthQ (UUE Λ F F''), memOrthQ]`. Introduce `h hh`. Express the relevant statement in the definitionally equal form `h ∈ Hp Λ F F'' at hh`. Rewrite `hh` using `[← hTh]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hh`.

Rewrite `hp` using `[memThPairsQ]`. Establish `hp1 : p.1 ∈ orth S (UUE Λ F F')` using `hp.1.1.1`. Establish `hy1 : y ∈ UUE Λ F F'` using `hy.1`. Establish `hy2 : y ∈ orth S (Xplus F)` using `hy.2`. Establish `e1 : S.hT p.1 y = 0` using `hTCommQ.mp ((memOrthQ.mp hp1) y hy1)`.

Establish `e2 : S.hT (p.1 - p.2) y = 0` using `memOrthQ.mp (orthAntiQ (XspLeXplusQ F) hy2) _ hp.1.2`. Use `show S.hT p.2 y = 0`. Establish `e : p.2 = p.1 - (p.1 - p.2)` using `by abel`. Rewrite using `[e, map_sub, LinearMap.sub_apply, e1, e2, sub_zero]`.
-/
theorem yliftMemQ (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ Ylift Λ F F') :
    y ∈ UUE Λ F F'' := by
  rw [← orthOrthQ (UUE Λ F F''), memOrthQ]
  intro h hh
  change h ∈ Hp Λ F F'' at hh
  rw [← hTh] at hh
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
  rw [memThPairsQ] at hp
  have hp1 : p.1 ∈ orth S (UUE Λ F F') := hp.1.1.1
  have hy1 : y ∈ UUE Λ F F' := hy.1
  have hy2 : y ∈ orth S (Xplus F) := hy.2
  have e1 : S.hT p.1 y = 0 := hTCommQ.mp ((memOrthQ.mp hp1) y hy1)
  have e2 : S.hT (p.1 - p.2) y = 0 := memOrthQ.mp (orthAntiQ (XspLeXplusQ F) hy2) _ hp.1.2
  show S.hT p.2 y = 0
  have e : p.2 = p.1 - (p.1 - p.2) := by abel
  rw [e, map_sub, LinearMap.sub_apply, e1, e2, sub_zero]

/- English proof (translation)
Rewrite using `[← orthOrthQ (UUE Λ F F''), memOrthQ]`. Introduce `h hh`. Express the relevant statement in the definitionally equal form `h ∈ Hp Λ F F'' at hh`. Rewrite `hh` using `[← hTh]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hh`.

Rewrite `hp` using `[memThPairsQ]`. Establish `hp1 : p.1 ∈ orth S (UUE Λ F F')` using `hp.1.1.1`. Establish `hy1 : y ∈ UUE Λ F F'` using `hy.1`. Establish `hy2 : y ∈ orth S (Xplus F')` using `hy.2`. Establish `e1 : S.hT (β p.1) (β y) = 0`.

Establish `e : S.hT (β p.1) (β y) = S.hT p.1 y` using `hi p.1 y`. Rewrite using `[e]`. Conclude with `hTCommQ.mp ((memOrthQ.mp hp1) y hy1)`. Establish `e2 : S.hT (β p.1 - p.2) (β y) = 0` using `memOrthQ.mp (mapOrthXQ hi hX (orthAntiQ (XspLeXplusQ F') hy2)) _ hp.2`. Use `show S.hT p.2 (β y) = 0`.

Establish `e : p.2 = β p.1 - (β p.1 - p.2)` using `by abel`. Rewrite using `[e, map_sub, LinearMap.sub_apply, e1, e2, sub_zero]`.
-/
theorem ylift'MemQ (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ Ylift' Λ F F') :
    β y ∈ UUE Λ F F'' := by
  rw [← orthOrthQ (UUE Λ F F''), memOrthQ]
  intro h hh
  change h ∈ Hp Λ F F'' at hh
  rw [← hTh] at hh
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
  rw [memThPairsQ] at hp
  have hp1 : p.1 ∈ orth S (UUE Λ F F') := hp.1.1.1
  have hy1 : y ∈ UUE Λ F F' := hy.1
  have hy2 : y ∈ orth S (Xplus F') := hy.2
  have e1 : S.hT (β p.1) (β y) = 0 := by
    have e : S.hT (β p.1) (β y) = S.hT p.1 y := hi p.1 y
    rw [e]
    exact hTCommQ.mp ((memOrthQ.mp hp1) y hy1)
  have e2 : S.hT (β p.1 - p.2) (β y) = 0 :=
    memOrthQ.mp (mapOrthXQ hi hX (orthAntiQ (XspLeXplusQ F') hy2)) _ hp.2
  show S.hT p.2 (β y) = 0
  have e : p.2 = β p.1 - (β p.1 - p.2) := by abel
  rw [e, map_sub, LinearMap.sub_apply, e1, e2, sub_zero]

end Theta

section Scalar

variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ} {T T' : E} {F : LFlag S r T}
  {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V}

/- English proof (translation)
Take `⟨x, hx, x', hx', e⟩` from `h`. Use `⟨x - (y - u), (Xsp F).sub_mem hx hu, x' - (u' - y'), (Xsp F').sub_mem hx' hu', ?_⟩` and prove the remaining obligations. Establish `e' : u - u' = (y - y') - (y - u) - (u' - y')` using `by abel`. Rewrite using `[e', e]`. Normalize the expressions using the abelian group laws.
-/
theorem sgShiftQ {y y' u u' : S.V} {al al' : E} (h : SgRel F F' y y' al al') (hu : y - u ∈ Xsp F)
    (hu' : u' - y' ∈ Xsp F') : SgRel F F' u u' al al' := by
  obtain ⟨x, hx, x', hx', e⟩ := h
  refine ⟨x - (y - u), (Xsp F).sub_mem hx hu, x' - (u' - y'), (Xsp F').sub_mem hx' hu', ?_⟩
  have e' : u - u' = (y - y') - (y - u) - (u' - y') := by abel
  rw [e', e]
  abel

/- English proof (translation)
Introduce `y1 _ y2 _ y1' _ y2'' _ h12 h21 al al'`. Establish `h21' : y2'' - y1' ∈ Xsp F'` using `h21`. Use `⟨fun h => sgShiftQ h h12 h21', fun h => sgShiftQ h ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_sub]`. Conclude with `neg_mem h12`.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem h21'`.
-/
theorem scalarReflQ : IsScalar Λ F F' F' (LinearEquiv.refl E S.V) := by
  intro y1 _ y2 _ y1' _ y2'' _ h12 h21 al al'
  have h21' : y2'' - y1' ∈ Xsp F' := h21
  refine ⟨fun h => sgShiftQ h h12 h21', fun h => sgShiftQ h ?_ ?_⟩
  · rw [← neg_sub]
    exact neg_mem h12
  · rw [← neg_sub]
    exact neg_mem h21'

/- English proof (translation)
Introduce `y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h21 al al'`. Establish `a : y2 - y1 ∈ Xsp F`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem h12`. Establish `b : y1' - β y2'' ∈ Xsp F''`.

Establish `e : y1' - β y2'' = -(β (y2'' - β.symm y1'))`. Rewrite using `[map_sub, LinearEquiv.apply_symm_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `neg_mem (mapXQ hX h21)`.

Conclude with `(hS y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' a b al al').symm`.
-/
theorem scalarSymmQ (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j)
    (hS : IsScalar Λ F F' F'' β) : IsScalar Λ F F'' F' β.symm := by
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h21 al al'
  have a : y2 - y1 ∈ Xsp F := by
    rw [← neg_sub]
    exact neg_mem h12
  have b : y1' - β y2'' ∈ Xsp F'' := by
    have e : y1' - β y2'' = -(β (y2'' - β.symm y1')) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]
      abel
    rw [e]
    exact neg_mem (mapXQ hX h21)
  exact (hS y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' a b al al').symm

end Scalar

section Rel

variable {Λ : Submodule (𝓞 E) S.V} {r k g : ℕ} {T T' : E} {F : LFlag S r T}
  {F' F'' F''' : LFlag S r T'}

/- English proof (translation)
Establish `n'` using `ndOfQ hΛ hF hL' hG'`. Use `⟨LinearEquiv.refl E S.V, pairReflQ, scalar_factor_eq_one_of_le hdim n' ?_, scalarReflQ⟩` and prove the remaining obligations. Introduce `x hx`. Use `Submodule.mem_map.mpr ⟨(x, x), memThPairsQ.mpr ⟨⟨⟨hx, hx⟩, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem relReflQ (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) :
    PI.ScalPairs.ScalRel Λ g k F F' F' := by
  have n' := ndOfQ hΛ hF hL' hG'
  refine ⟨LinearEquiv.refl E S.V, pairReflQ, scalar_factor_eq_one_of_le hdim n' ?_, scalarReflQ⟩
  intro x hx
  refine Submodule.mem_map.mpr ⟨(x, x), memThPairsQ.mpr ⟨⟨⟨hx, hx⟩, ?_⟩, ?_⟩, rfl⟩
  · simp
  · simp

/- English proof (translation)
Take `⟨β, hP, hs, hS⟩` from `h`. Establish `n'` using `ndOfQ hΛ hF hL' hG'`. Establish `n''` using `ndOfQ hΛ hF hL'' hG''`. Use `⟨β.symm, pairSymmQ hP, scalar_factor_eq_one_of_le hdim n'' ?_, scalarSymmQ hP.2.1 hS⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← thEq''Q hΛ hdim n' n'' hs]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hx`. Rewrite `hp` using `[memThPairsQ]`. Use `Submodule.mem_map.mpr ⟨(p.2, p.1), memThPairsQ.mpr ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show p.2 - p.1 ∈ Xsp F`.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem hp.1.2`. Use `show β.symm p.2 - p.1 ∈ Xsp F'`. Establish `e : β.symm p.2 - p.1 = -(β.symm (β p.1 - p.2))`. Rewrite using `[map_sub, LinearEquiv.symm_apply_apply]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `neg_mem (mapXQ (XflagSymmQ hP.2.1) hp.2)`.
-/
theorem relSymmQ (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (h : PI.ScalPairs.ScalRel Λ g k F F' F'') :
    PI.ScalPairs.ScalRel Λ g k F F'' F' := by
  obtain ⟨β, hP, hs, hS⟩ := h
  have n' := ndOfQ hΛ hF hL' hG'
  have n'' := ndOfQ hΛ hF hL'' hG''
  refine ⟨β.symm, pairSymmQ hP, scalar_factor_eq_one_of_le hdim n'' ?_, scalarSymmQ hP.2.1 hS⟩
  intro x hx
  rw [← thEq''Q hΛ hdim n' n'' hs] at hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  rw [memThPairsQ] at hp
  refine Submodule.mem_map.mpr ⟨(p.2, p.1), memThPairsQ.mpr ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, ?_⟩, ?_⟩, rfl⟩
  · show p.2 - p.1 ∈ Xsp F
    rw [← neg_sub]
    exact neg_mem hp.1.2
  · show β.symm p.2 - p.1 ∈ Xsp F'
    have e : β.symm p.2 - p.1 = -(β.symm (β p.1 - p.2)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [e]
    exact neg_mem (mapXQ (XflagSymmQ hP.2.1) hp.2)

/- English proof (translation)
Take `⟨β, hP1, hs1, hS1⟩` from `h1`. Take `⟨γ, hP2, hs2, hS2⟩` from `h2`. Establish `n'` using `ndOfQ hΛ hF hL' hG'`. Establish `n''` using `ndOfQ hΛ hF hL'' hG''`. Establish `hTh1` using `thEqQ hdim n' hs1`.

Establish `hTh2` using `thEqQ hdim n'' hs2`. Establish `hTh1''` using `thEq''Q hΛ hdim n' n'' hs1`. Use `⟨β.trans γ, pairTransQ hP1 hP2, scalar_factor_eq_one_of_le hdim n' ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← hTh1]`.

Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hx`. Rewrite `hp` using `[memThPairsQ]`. Establish `hq0 : p.2 ∈ Th Λ F F'' F''' γ`. Rewrite using `[hTh2]`. Conclude with `hp.1.1.2`.

Take `⟨q, hq, hq1⟩` from `Submodule.mem_map.mp hq0`. Rewrite `hq` using `[memThPairsQ]`. Express the relevant statement in the definitionally equal form `q.1 = p.2 at hq1`. Use `Submodule.mem_map.mpr ⟨(p.1, q.2), memThPairsQ.mpr ⟨⟨⟨hp.1.1.1, hq.1.1.2⟩, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show p.1 - q.2 ∈ Xsp F`.

Establish `e : p.1 - q.2 = (p.1 - p.2) + (q.1 - q.2)`. Rewrite using `[hq1]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `add_mem hp.1.2 hq.1.2`.

Use `show γ (β p.1) - q.2 ∈ Xsp F'''`. Establish `e : γ (β p.1) - q.2 = γ (β p.1 - p.2) + (γ q.1 - q.2)`. Rewrite using `[map_sub, hq1]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `add_mem (mapXQ hP2.2.1 hp.2) hq.2`. Introduce `y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'`. Establish `hy1b : y1 ∈ orth S (Xplus F)` using `hy1.2`. Establish `hy1'b : y1' ∈ orth S (Xplus F')` using `hy1'.2`. Establish `hy2 : y1 ∈ Ylift Λ F F''` using `Submodule.mem_inf.mpr ⟨yliftMemQ hTh1'' hy1, hy1b⟩`.

Establish `hy2' : β y1' ∈ Ylift' Λ F F''` using `Submodule.mem_inf.mpr ⟨ylift'MemQ hP1.1.1 hP1.2.1 hTh1'' hy1', mapOrthXplusQ hP1.1.1 hP1.2.1 hP1.2.2.1 hy1'b⟩`. Establish `a` using `hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'`. Establish `b` using `hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'`. Conclude with `a.trans b`.
-/
theorem relTransQ (hΛ : Submodule.IsLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (h1 : PI.ScalPairs.ScalRel Λ g k F F' F'')
    (h2 : PI.ScalPairs.ScalRel Λ g k F F'' F''') :
    PI.ScalPairs.ScalRel Λ g k F F' F''' := by
  obtain ⟨β, hP1, hs1, hS1⟩ := h1
  obtain ⟨γ, hP2, hs2, hS2⟩ := h2
  have n' := ndOfQ hΛ hF hL' hG'
  have n'' := ndOfQ hΛ hF hL'' hG''
  have hTh1 := thEqQ hdim n' hs1
  have hTh2 := thEqQ hdim n'' hs2
  have hTh1'' := thEq''Q hΛ hdim n' n'' hs1
  refine ⟨β.trans γ, pairTransQ hP1 hP2, scalar_factor_eq_one_of_le hdim n' ?_, ?_⟩
  · intro x hx
    rw [← hTh1] at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    rw [memThPairsQ] at hp
    have hq0 : p.2 ∈ Th Λ F F'' F''' γ := by
      rw [hTh2]
      exact hp.1.1.2
    obtain ⟨q, hq, hq1⟩ := Submodule.mem_map.mp hq0
    rw [memThPairsQ] at hq
    change q.1 = p.2 at hq1
    refine Submodule.mem_map.mpr ⟨(p.1, q.2), memThPairsQ.mpr ⟨⟨⟨hp.1.1.1, hq.1.1.2⟩, ?_⟩, ?_⟩, rfl⟩
    · show p.1 - q.2 ∈ Xsp F
      have e : p.1 - q.2 = (p.1 - p.2) + (q.1 - q.2) := by
        rw [hq1]
        abel
      rw [e]
      exact add_mem hp.1.2 hq.1.2
    · show γ (β p.1) - q.2 ∈ Xsp F'''
      have e : γ (β p.1) - q.2 = γ (β p.1 - p.2) + (γ q.1 - q.2) := by
        rw [map_sub, hq1]
        abel
      rw [e]
      exact add_mem (mapXQ hP2.2.1 hp.2) hq.2
  · intro y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'
    have hy1b : y1 ∈ orth S (Xplus F) := hy1.2
    have hy1'b : y1' ∈ orth S (Xplus F') := hy1'.2
    have hy2 : y1 ∈ Ylift Λ F F'' :=
      Submodule.mem_inf.mpr ⟨yliftMemQ hTh1'' hy1, hy1b⟩
    have hy2' : β y1' ∈ Ylift' Λ F F'' :=
      Submodule.mem_inf.mpr ⟨ylift'MemQ hP1.1.1 hP1.2.1 hTh1'' hy1',
        mapOrthXplusQ hP1.1.1 hP1.2.1 hP1.2.2.1 hy1'b⟩
    have a := hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'
    have b := hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'
    exact a.trans b

end Rel

/- English proof (translation)
Introduce `E _ _ _ S r k g hdim Λ hΛ T T' _ _ F hF`. Use `⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩` and prove the remaining obligations. Conclude with `relReflQ hΛ hdim hF x.2.1 x.2.2`. Conclude with `relSymmQ hΛ hdim hF x.2.1 x.2.2 y.2.1 y.2.2 h`. Conclude with `relTransQ hΛ hdim hF x.2.1 x.2.2 y.2.1 y.2.2 h1 h2`.
-/
theorem scalarEquivG_holds : PI.ScalPairs.ScalarEquivG := by
  intro E _ _ _ S r k g hdim Λ hΛ T T' _ _ F hF
  refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
  · exact relReflQ hΛ hdim hF x.2.1 x.2.2
  · exact relSymmQ hΛ hdim hF x.2.1 x.2.2 y.2.1 y.2.2 h
  · exact relTransQ hΛ hdim hF x.2.1 x.2.2 y.2.1 y.2.2 h1 h2

end PI.UnitaryGroupMassFormula.ScalEquivGen
