import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Ideal.mul_mem_right _ _ ha.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩`.
-/
theorem int_mul {x : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = x)) (hb : b ∈ intAt D (· = x)) : a * b ∈ intAt D (· = x) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩`.
-/
theorem int_neg {x : Pl D} {a : AE D} : -a ∈ intAt D (· = x) ↔ a ∈ intAt D (· = x) :=
  ⟨fun h => by simpa using GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩

/- English proof (translation)
Rewrite `ha`, the goal using `[mem_idAt_iff]`. Rewrite using `[← cA_idem, ← RingHom.map_mul, ha]`.
-/
theorem id_conj {x : Pl D} {a : AE D} (ha : a ∈ idAt D (· = x)) : cA D a ∈ idAt D (· = x) := by
  rw [mem_idAt_iff] at ha ⊢
  rw [← cA_idem, ← RingHom.map_mul, ha]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨by simpa only [cA_cA] using id_conj h.1, (FrameLat.cA_int_iff a).1 h.2⟩, fun h => ⟨id_conj h.1, (FrameLat.cA_int_iff a).2 h.2⟩⟩`.
-/
theorem int_conj {x : Pl D} {a : AE D} : cA D a ∈ intAt D (· = x) ↔ a ∈ intAt D (· = x) :=
  ⟨fun h => ⟨by simpa only [cA_cA] using id_conj h.1, (FrameLat.cA_int_iff a).1 h.2⟩,
    fun h => ⟨id_conj h.1, (FrameLat.cA_int_iff a).2 h.2⟩⟩

def IsU (x : Pl D) (u : AE D) : Prop := ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ u * a ∈ intAt D (· = x)

/- English proof (translation)
Introduce `a _` and use `by rw [one_mul]`.
-/
theorem IsU.one (x : Pl D) : IsU x 1 := fun a _ => by rw [one_mul]

/- English proof (translation)
Introduce `a ha` and use `by rw [hv a ha, hu _ (Ideal.mul_mem_left _ _ ha), mul_assoc]`.
-/
theorem IsU.mul {x : Pl D} {u v : AE D} (hu : IsU x u) (hv : IsU x v) : IsU x (u * v) := fun a ha => by
  rw [hv a ha, hu _ (Ideal.mul_mem_left _ _ ha), mul_assoc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `IsU.one x`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hu`.
-/
theorem IsU.pow {x : Pl D} {u : AE D} (hu : IsU x u) (n : ℕ) : IsU x (u ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsU.one x
  | succ n ih => rw [pow_succ]; exact ih.mul hu

/- English proof (translation)
Introduce `a ha` and use `by rw [neg_mul, int_neg, hu a ha]`.
-/
theorem IsU.neg {x : Pl D} {u : AE D} (hu : IsU x u) : IsU x (-u) := fun a ha => by
  rw [neg_mul, int_neg, hu a ha]

/- English proof (translation)
Introduce `a ha` and use `by rw [← int_conj, hu _ (id_conj ha), ← int_conj, RingHom.map_mul, cA_cA]`.
-/
theorem IsU.conj {x : Pl D} {u : AE D} (hu : IsU x u) : IsU x (cA D u) := fun a ha => by
  rw [← int_conj, hu _ (id_conj ha), ← int_conj, RingHom.map_mul, cA_cA]

/- English proof (translation)
Introduce `a ha` and use `by rw [hu _ (Ideal.mul_mem_left _ v ha), ← mul_assoc, h, one_mul]`.
-/
theorem IsU.inv {x : Pl D} {u v : AE D} (hu : IsU x u) (h : u * v = 1) : IsU x v := fun a ha => by
  rw [hu _ (Ideal.mul_mem_left _ v ha), ← mul_assoc, h, one_mul]

/- English proof (translation)
Introduce `a _` and use `⟨hu a, fun h' => by simpa only [← mul_assoc, mul_comm v u, h, one_mul] using hv _ h'⟩`.
-/
theorem IsU.of_pres {x : Pl D} {u v : AE D} (h : u * v = 1) (hu : ∀ a ∈ intAt D (· = x), u * a ∈ intAt D (· = x))
    (hv : ∀ a ∈ intAt D (· = x), v * a ∈ intAt D (· = x)) : IsU x u := fun a _ =>
  ⟨hu a, fun h' => by simpa only [← mul_assoc, mul_comm v u, h, one_mul] using hv _ h'⟩

def cU (u : (AE D)ˣ) : (AE D)ˣ := Units.map (cA D).toMonoidHom u

def inU (e : D.host.E) (he : e ≠ 0) : (AE D)ˣ := Units.map (incA D).toMonoidHom (Units.mk0 e he)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cU_val (u : (AE D)ˣ) : ((cU u : (AE D)ˣ) : AE D) = cA D u := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cU_inv (u : (AE D)ˣ) : (((cU u)⁻¹ : (AE D)ˣ) : AE D) = cA D ((u⁻¹ : (AE D)ˣ) : AE D) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inU_val (e : D.host.E) (he : e ≠ 0) : ((inU e he : (AE D)ˣ) : AE D) = incA D e := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inU_inv (e : D.host.E) (he : e ≠ 0) : (((inU e he)⁻¹ : (AE D)ˣ) : AE D) = incA D e⁻¹ := rfl

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨w, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ _ _ => rfl⟩`. Consider the case `insert y S hy ih`. Take `⟨μ, h1, h2⟩` from `ih`. Establish `he` using `idem_mul_self (D := D) (· = y)`.

Use `set e := idem D (· = y) with hedef`. Establish `hk : (e * u y + (1 - e) * μ) * (e * ((u y)⁻¹ : (AE D)ˣ) + (1 - e) * (μ⁻¹ : (AE D)ˣ)) = 1`. Establish `a1` using `(u y).mul_inv`. Establish `a2` using `μ.mul_inv`. Take the linear combination `(e * e) * a1 + ((1 - e) * (1 - e)) * a2 + (2 - (u y : AE D) * (μ⁻¹ : (AE D)ˣ) - (μ : AE D) * ((u y)⁻¹ : (AE D)ˣ)) * he`.

Establish `hoff : ∀ x, x ≠ y → ∀ a ∈ idAt D (· = x), e * a = 0` using `fun x hx a ha => by`. Rewrite using `[hedef, ← mem_idOff_iff]`. Use `(Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 (compAt_of_idAt ha ?_)` and prove the remaining obligations. Rewrite using `[w.2]`. Conclude with `hx.symm`.

Establish `hmv : ∀ x, x ≠ y → ∀ a ∈ idAt D (· = x), (e * u y + (1 - e) * μ) * a = μ * a` using `fun x hx a ha => by`. Take the linear combination `((u y : AE D) - μ) * hoff x hx a ha`. Use `⟨Units.mkOfMulEqOne _ _ hk, fun x hx a ha => ?_, fun x hx a ha => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e * u y + (1 - e) * μ) * a = _`. Distinguish the cases in `hxy : x = y`.

Substitute `hxy` using the available equality. Take the linear combination `((u x : AE D) - μ) * (mem_idAt_iff _ a).1 ha`. Rewrite using `[hmv x hxy a ha, h1 x ((Finset.mem_insert.1 hx).resolve_left hxy) a ha]`. Express the relevant statement in the definitionally equal form `(e * u y + (1 - e) * μ) * a = _`. Rewrite `hx` using `[Finset.mem_insert, not_or]`.

Rewrite using `[hmv x hx.1 a ha, h2 x hx.2 a ha]`.
-/
theorem patch (S : Finset (Pl D)) (u : Pl D → (AE D)ˣ) (w : (AE D)ˣ) : ∃ μ : (AE D)ˣ,
    (∀ x ∈ S, ∀ a ∈ idAt D (· = x), (μ : AE D) * a = u x * a) ∧ ∀ x, x ∉ S → ∀ a ∈ idAt D (· = x), (μ : AE D) * a = w * a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨w, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ _ _ => rfl⟩
  | insert y S hy ih =>
    obtain ⟨μ, h1, h2⟩ := ih
    have he := idem_mul_self (D := D) (· = y)
    set e := idem D (· = y) with hedef
    have hk : (e * u y + (1 - e) * μ) * (e * ((u y)⁻¹ : (AE D)ˣ) + (1 - e) * (μ⁻¹ : (AE D)ˣ)) = 1 := by
      have a1 := (u y).mul_inv
      have a2 := μ.mul_inv
      linear_combination (e * e) * a1 + ((1 - e) * (1 - e)) * a2 +
        (2 - (u y : AE D) * (μ⁻¹ : (AE D)ˣ) - (μ : AE D) * ((u y)⁻¹ : (AE D)ˣ)) * he
    have hoff : ∀ x, x ≠ y → ∀ a ∈ idAt D (· = x), e * a = 0 := fun x hx a ha => by
      rw [hedef, ← mem_idOff_iff]
      refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 (compAt_of_idAt ha ?_)
      rw [w.2]; exact hx.symm
    have hmv : ∀ x, x ≠ y → ∀ a ∈ idAt D (· = x), (e * u y + (1 - e) * μ) * a = μ * a := fun x hx a ha => by
      linear_combination ((u y : AE D) - μ) * hoff x hx a ha
    refine ⟨Units.mkOfMulEqOne _ _ hk, fun x hx a ha => ?_, fun x hx a ha => ?_⟩
    · change (e * u y + (1 - e) * μ) * a = _
      by_cases hxy : x = y
      · subst hxy
        linear_combination ((u x : AE D) - μ) * (mem_idAt_iff _ a).1 ha
      · rw [hmv x hxy a ha, h1 x ((Finset.mem_insert.1 hx).resolve_left hxy) a ha]
    · change (e * u y + (1 - e) * μ) * a = _
      rw [Finset.mem_insert, not_or] at hx
      rw [hmv x hx.1 a ha, h2 x hx.2 a ha]

/- English proof (translation)
Introduce `a ha` and use `by have := h _ (Ideal.mul_mem_left _ ((u⁻¹ : (AE D)ˣ) : AE D) ha) rw [Units.mul_inv_cancel_left] at this rw [← this, Units.inv_mul_cancel_left, this]`.
-/
theorem inv_same {x : Pl D} {μ u : (AE D)ˣ} (h : ∀ a ∈ idAt D (· = x), (μ : AE D) * a = u * a) :
    ∀ a ∈ idAt D (· = x), ((μ⁻¹ : (AE D)ˣ) : AE D) * a = (u⁻¹ : (AE D)ˣ) * a := fun a ha => by
  have := h _ (Ideal.mul_mem_left _ ((u⁻¹ : (AE D)ˣ) : AE D) ha)
  rw [Units.mul_inv_cancel_left] at this
  rw [← this, Units.inv_mul_cancel_left, this]

/- English proof (translation)
Simplify using `only [hermAt, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem herm_eq (S : HSp D) (x y : Fin S.rank → AE D) : hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, RingHom.map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem herm_smul (S : HSp D) (a b : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) (b • y) = a * cA D b * hermAt S x y := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, RingHom.map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hermAt, map_sum, RingHom.map_mul, cA_cA]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: cA D (gA S j i) = gA S i j` using `congrFun (congrFun (adj_gA S) i) j`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_conj (S : HSp D) (x y : Fin S.rank → AE D) : cA D (hermAt S x y) = hermAt S y x := by
  simp only [hermAt, map_sum, RingHom.map_mul, cA_cA]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : cA D (gA S j i) = gA S i j := congrFun (congrFun (adj_gA S) i) j
  rw [this]; ring

/- English proof (translation)
Simplify using `only [hermAt, dotProduct, mulVec, Finset.mul_sum, map_sum, RingHom.map_mul, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem herm_rat (S : HSp D) (z : Fin S.rank → D.host.E) :
    hermAt S (ratV z) (ratV z) = incA D (star z ⬝ᵥ S.gram *ᵥ z) := by
  simp only [hermAt, dotProduct, mulVec, Finset.mul_sum, map_sum, RingHom.map_mul, mul_assoc]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (incA D) M z i).symm`.
-/
theorem rat_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    (rat M : Mx D m n) *ᵥ ratV z = ratV (M *ᵥ z) := by
  funext i
  exact (RingHom.map_mulVec (incA D) M z i).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mul (incA D) a (z i)`.
-/
theorem ratV_smul {n : ℕ} (a : D.host.E) (z : Fin n → D.host.E) : (ratV (a • z) : Fin n → AE D) = incA D a • ratV z := by
  funext i
  exact RingHom.map_mul (incA D) a (z i)

/- English proof (translation)
Establish `h1` using `h.1`. Use `⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega), fun h0 => h.2 ?_⟩` and prove the remaining obligations. Establish `: ζ = 0` using `funext fun i => by`. Rewrite using `[show i = ⟨0, by omega⟩ from Fin.ext (by have := i.2; simp only; omega)]; exact h0`. Rewrite using `[this, mulVec_zero, dotProduct_zero]`.
-/
theorem line_coord {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) :
    ∃ i₀ : Fin L.rank, (∀ i, i = i₀) ∧ ζ i₀ ≠ 0 := by
  have h1 := h.1
  refine ⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega), fun h0 => h.2 ?_⟩
  have : ζ = 0 := funext fun i => by
    rw [show i = ⟨0, by omega⟩ from Fin.ext (by have := i.2; simp only; omega)]; exact h0
  rw [this, mulVec_zero, dotProduct_zero]

/- English proof (translation)
Take `⟨i₀, hi, h0⟩` from `line_coord h`. Use `⟨incA D (ζ i₀)⁻¹ * y i₀, Ideal.mul_mem_left _ _ (hy i₀), funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hi i]`. Express the relevant statement in the definitionally equal form `_ = incA D (ζ i₀)⁻¹ * y i₀ * incA D (ζ i₀)`. Rewrite using `[mul_right_comm, ← RingHom.map_mul, inv_mul_cancel₀ h0, RingHom.map_one, one_mul]`.
-/
theorem line_vec {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) {x : Pl D} {y : Fin L.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (· = x)) : ∃ a ∈ idAt D (· = x), y = a • ratV ζ := by
  obtain ⟨i₀, hi, h0⟩ := line_coord h
  refine ⟨incA D (ζ i₀)⁻¹ * y i₀, Ideal.mul_mem_left _ _ (hy i₀), funext fun i => ?_⟩
  rw [hi i]
  change _ = incA D (ζ i₀)⁻¹ * y i₀ * incA D (ζ i₀)
  rw [mul_right_comm, ← RingHom.map_mul, inv_mul_cancel₀ h0, RingHom.map_one, one_mul]

/- English proof (translation)
Take `⟨i₀, hi, h0⟩` from `line_coord h`. Set `I : Submodule (𝓞 D.host.E) D.host.E` to `Λ.map (LinearMap.proj (R := 𝓞 D.host.E) (φ := fun _ => D.host.E) i₀)`. Establish `hI : I.FG` using `hΛ.fg.map _`. Set `𝔞 : FI D` to `⟨I, FractionalIdeal.isFractional_of_fg hI⟩`. Establish `hc : ∀ y : Fin L.rank → D.host.E, y = fun _ => y i₀` using `fun y => funext fun i => by rw [hi i]`.

Establish `h𝔞 : 𝔞 ≠ 0` using `fun h' => by`. Establish `h1 : ∀ y ∈ Λ, y = 0` using `fun y hy => by`. Establish `: y i₀ = 0` using `FractionalIdeal.eq_zero_iff.1 h' _ ⟨y, hy, rfl⟩`. Rewrite using `[hc y, this]`. Both sides reduce to the same expression.

Establish `h2 : Submodule.span D.host.E (Λ : Set (Fin L.rank → D.host.E)) ≤ ⊥` using `Submodule.span_le.2 h1`. Rewrite `h2` using `[hΛ.span_eq_top]`. Conclude with `h0 (congrFun (h2 (Submodule.mem_top (x := ζ))) i₀)`. Take `⟨g, hg, hgen⟩` from `GlobalTheory.IdVGen.idV_gen D x 𝔞 h𝔞`. Establish `key : ∀ y : Fin L.rank → AE D, y ∈ latV L Λ (· = x) ↔ y i₀ ∈ idV 𝔞 x` using `fun y => by`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, h0, a, rfl, z, hz, rfl⟩` from `hy`.

Conclude with `AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, ⟨z, hz, rfl⟩, by simp only [one_mul]⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `neg a _ ha => exact neg_mem ha`. Introduce `hy`.

Establish `: ∀ s ∈ idV 𝔞 x, (fun _ => s) ∈ latV L Λ (· = x)` using `fun s hs => by`. Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, h0, _, ⟨z, hz, rfl⟩, rfl⟩` from `hy`. Conclude with `AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, z, hz, funext fun i => by rw [one_mul, hi i]; rfl⟩`.

Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `neg a _ ha => exact neg_mem ha`. Establish `h3 : y = fun _ => y i₀` using `funext fun i => by rw [hi i]`. Rewrite using `[h3]`.

Conclude with `this _ hy`. Use `⟨g * (ζ i₀)⁻¹, mul_ne_zero hg (inv_ne_zero h0), fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[key, hgen]`. Express the relevant statement in the definitionally equal form `incA D g⁻¹ * (a * incA D (ζ i₀)) ∈ _ ∧ a * incA D (ζ i₀) ∈ _ ↔ _`. Rewrite using `[and_iff_left (Ideal.mul_mem_right _ _ ha), mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]`.
-/
theorem line_gen {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) {Λ : Lat L}
    (hΛ : Submodule.IsLattice D.host.E Λ) (x : Pl D) : ∃ e : D.host.E, e ≠ 0 ∧ ∀ a ∈ idAt D (· = x),
      a • ratV ζ ∈ latV L Λ (· = x) ↔ incA D e⁻¹ * a ∈ intAt D (· = x) := by
  obtain ⟨i₀, hi, h0⟩ := line_coord h
  let I : Submodule (𝓞 D.host.E) D.host.E := Λ.map (LinearMap.proj (R := 𝓞 D.host.E) (φ := fun _ => D.host.E) i₀)
  have hI : I.FG := hΛ.fg.map _
  let 𝔞 : FI D := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hc : ∀ y : Fin L.rank → D.host.E, y = fun _ => y i₀ := fun y => funext fun i => by rw [hi i]
  have h𝔞 : 𝔞 ≠ 0 := fun h' => by
    have h1 : ∀ y ∈ Λ, y = 0 := fun y hy => by
      have : y i₀ = 0 := FractionalIdeal.eq_zero_iff.1 h' _ ⟨y, hy, rfl⟩
      rw [hc y, this]; rfl
    have h2 : Submodule.span D.host.E (Λ : Set (Fin L.rank → D.host.E)) ≤ ⊥ := Submodule.span_le.2 h1
    rw [hΛ.span_eq_top] at h2
    exact h0 (congrFun (h2 (Submodule.mem_top (x := ζ))) i₀)
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D x 𝔞 h𝔞
  have key : ∀ y : Fin L.rank → AE D, y ∈ latV L Λ (· = x) ↔ y i₀ ∈ idV 𝔞 x := fun y => by
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, ⟨z, hz, rfl⟩, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    · intro hy
      have : ∀ s ∈ idV 𝔞 x, (fun _ => s) ∈ latV L Λ (· = x) := fun s hs => by
        induction hs using AddSubgroup.closure_induction with
        | mem y hy =>
          obtain ⟨α, hα, h0, _, ⟨z, hz, rfl⟩, rfl⟩ := hy
          exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, z, hz, funext fun i => by rw [one_mul, hi i]; rfl⟩
        | zero => exact zero_mem _
        | add a b _ _ ha hb => exact add_mem ha hb
        | neg a _ ha => exact neg_mem ha
      have h3 : y = fun _ => y i₀ := funext fun i => by rw [hi i]
      rw [h3]; exact this _ hy
  refine ⟨g * (ζ i₀)⁻¹, mul_ne_zero hg (inv_ne_zero h0), fun a ha => ?_⟩
  rw [key, hgen]
  change incA D g⁻¹ * (a * incA D (ζ i₀)) ∈ _ ∧ a * incA D (ζ i₀) ∈ _ ↔ _
  rw [and_iff_left (Ideal.mul_mem_right _ _ ha), mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]

/- English proof (translation)
Introduce `a ha` and use `by have hsd := LocSD.isSDAt_latV D L Λ x hΛ have h1 := hμ _ (Ideal.mul_mem_left _ (μ : AE D) ha) rw [Units.inv_mul_cancel_left, hsd.2.2 (((μ : AE D) * a) • ratV ζ) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1 rw [← h1] have he := idem_mem_intAt (D := D) (· …`.
-/
theorem line_norm {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) {Λ : Lat L} (hΛ : IsSelfDualC L Λ) {x : Pl D}
    {μ : (AE D)ˣ} (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L Λ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    IsU x ((μ : AE D) * cA D μ * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D L Λ x hΛ
  have h1 := hμ _ (Ideal.mul_mem_left _ (μ : AE D) ha)
  rw [Units.inv_mul_cancel_left, hsd.2.2 (((μ : AE D) * a) • ratV ζ) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  have he := idem_mem_intAt (D := D) (· = x)
  constructor
  · intro H
    have := H _ ((hμ _ (Ideal.mul_mem_left _ (μ : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    rw [herm_smul, herm_rat, RingHom.map_mul, cA_idem] at this
    convert this using 1
    linear_combination (-(μ : AE D) * cA D μ * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * (mem_idAt_iff _ a).1 ha
  · intro H y hy
    obtain ⟨b, hb, rfl⟩ := line_vec h (hsd.1 y hy)
    have := int_mul H (int_conj.2 ((hμ b hb).1 hy))
    rw [herm_smul, herm_rat]
    convert this using 1
    have e : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
    rw [RingHom.map_mul]
    linear_combination (-(μ : AE D) * a * cA D b * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * e

/- English proof (translation)
Establish `e : (ratV (vecB o ζ) : Fin X.rank → AE D) = o.jB *ᵥ ratV ζ` using `(rat_mulVec _ _).symm`. Rewrite using `[h, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec, and_iff_right (zero_mem _)]`.
-/
theorem orth_line {X T L : HSp D} (o : OrthDec X T L) {Λ : Lat X} {ΛT : Lat T} {ΛL : Lat L} {x : Pl D}
    (h : OrthAt o Λ ΛT ΛL x) (ζ : Fin L.rank → D.host.E) (a : AE D) :
    a • ratV ζ ∈ latV L ΛL (· = x) ↔ a • ratV (vecB o ζ) ∈ latV X Λ (· = x) := by
  have e : (ratV (vecB o ζ) : Fin X.rank → AE D) = o.jB *ᵥ ratV ζ := (rat_mulVec _ _).symm
  rw [h, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec,
    and_iff_right (zero_mem _)]

/- English proof (translation)
Establish `h1 : ∀ x, ∃ u : (AE D)ˣ, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV (vecB o ζ) ∈ latV X Λ (· = x) ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)` using `fun x => by`. Distinguish the cases in `hx : P x`. Conclude with `⟨1, fun h' => absurd hx h'⟩`. Take `⟨ΛL, hL, ho⟩` from `h x hx`. Take `⟨e, he, hg⟩` from `line_gen hζ hL.1 x`.

Conclude with `⟨inU e he, fun _ a ha => by rw [← orth_line o ho, hg a ha, inU_inv]⟩`. Use `choose u hu using h1`. Establish `hz : vecB o ζ ≠ 0` using `fun h0 => by`. Take `⟨i₀, -, hi⟩` from `line_coord hζ`. Establish `: o.qB *ᵥ vecB o ζ = ζ` using `by rw [vecB, mulVec_mulVec, o.qB_iB, one_mulVec]`.

Rewrite `this` using `[h0, mulVec_zero]`. Conclude with `hi (congrFun this i₀).symm`. Take `⟨i₀, hi₀⟩` from `Function.ne_iff.1 hz`. Establish `hev : ∀ᶠ x : Pl D in cofinite, ∀ a ∈ idAt D (· = x), a • ratV (vecB o ζ) ∈ latV X Λ (· = x) ↔ a ∈ intAt D (· = x)` using `by filter_upwards [GlobalTheory.LatAlmostStd.eventually_latV_iff D X Λ hΛ, eventually_all.2 fun i => AeUnit.eventually_incA_mul_mem_intAt D (vecB o ζ i), AeUnit.eventually_incA_mul_mem_intAt D (vecB o ζ i₀)⁻¹] with x h1 h2 h3 a _`. Rewrite using `[h1]`.

Use `⟨fun H => ?_, fun H i => ?_⟩` and prove the remaining obligations. Use `h3 _ (H i₀)` as an intermediate fact. Express the relevant statement in the definitionally equal form `incA D (vecB o ζ i₀)⁻¹ * (a * incA D (vecB o ζ i₀)) ∈ _ at this`. Rewrite `this` using `[mul_comm a, ← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hi₀, RingHom.map_one, one_mul]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `a * incA D (vecB o ζ i) ∈ _`.

Rewrite using `[mul_comm]`. Conclude with `h2 i a H`. Establish `hfin` using `eventually_cofinite.1 hev`. Take `⟨μ, m1, m2⟩` from `patch hfin.toFinset u 1`. Use `⟨μ, fun x hx a ha => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hS : x ∈ hfin.toFinset`. Rewrite using `[inv_same (m1 x hS) a ha]`. Conclude with `hu x hx a ha`. Rewrite using `[inv_same (m2 x hS) a ha, inv_one, Units.val_one, one_mul]`. Rewrite `hS` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`.

Conclude with `hS a ha`.
-/
theorem line_idele {X T L : HSp D} (o : OrthDec X T L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {Λ : Lat X}
    (hΛ : Submodule.IsLattice D.host.E Λ) (ΛT : Lat T) (P : Pl D → Prop)
    (h : ∀ x, ¬ P x → ∃ ΛL : Lat L, IsSelfDualC L ΛL ∧ OrthAt o Λ ΛT ΛL x) :
    ∃ μ : (AE D)ˣ, ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x),
      a • ratV (vecB o ζ) ∈ latV X Λ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  have h1 : ∀ x, ∃ u : (AE D)ˣ, ¬ P x → ∀ a ∈ idAt D (· = x),
      a • ratV (vecB o ζ) ∈ latV X Λ (· = x) ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun x => by
    by_cases hx : P x
    · exact ⟨1, fun h' => absurd hx h'⟩
    · obtain ⟨ΛL, hL, ho⟩ := h x hx
      obtain ⟨e, he, hg⟩ := line_gen hζ hL.1 x
      exact ⟨inU e he, fun _ a ha => by rw [← orth_line o ho, hg a ha, inU_inv]⟩
  choose u hu using h1
  have hz : vecB o ζ ≠ 0 := fun h0 => by
    obtain ⟨i₀, -, hi⟩ := line_coord hζ
    have : o.qB *ᵥ vecB o ζ = ζ := by rw [vecB, mulVec_mulVec, o.qB_iB, one_mulVec]
    rw [h0, mulVec_zero] at this
    exact hi (congrFun this i₀).symm
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz
  have hev : ∀ᶠ x : Pl D in cofinite, ∀ a ∈ idAt D (· = x),
      a • ratV (vecB o ζ) ∈ latV X Λ (· = x) ↔ a ∈ intAt D (· = x) := by
    filter_upwards [GlobalTheory.LatAlmostStd.eventually_latV_iff D X Λ hΛ,
      eventually_all.2 fun i => AeUnit.eventually_incA_mul_mem_intAt D (vecB o ζ i),
      AeUnit.eventually_incA_mul_mem_intAt D (vecB o ζ i₀)⁻¹] with x h1 h2 h3 a _
    rw [h1]
    refine ⟨fun H => ?_, fun H i => ?_⟩
    · have := h3 _ (H i₀)
      change incA D (vecB o ζ i₀)⁻¹ * (a * incA D (vecB o ζ i₀)) ∈ _ at this
      rwa [mul_comm a, ← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hi₀, RingHom.map_one, one_mul] at this
    · change a * incA D (vecB o ζ i) ∈ _
      rw [mul_comm]; exact h2 i a H
  have hfin := eventually_cofinite.1 hev
  obtain ⟨μ, m1, m2⟩ := patch hfin.toFinset u 1
  refine ⟨μ, fun x hx a ha => ?_⟩
  by_cases hS : x ∈ hfin.toFinset
  · rw [inv_same (m1 x hS) a ha]; exact hu x hx a ha
  · rw [inv_same (m2 x hS) a ha, inv_one, Units.val_one, one_mul]
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hS
    exact hS a ha

/- English proof (translation)
Establish `h1` using `mulVec_mem_idAt d.pX h j`. Establish `h2 : (d.pX *ᵥ colMul d.jX j a) j = a * (d.pX ⬝ d.jX) j j`. Simplify using `only [mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Rewrite `h1` using `[h2, d.pX_jX, Matrix.one_apply_eq, mul_one]`. Then use the resulting hypothesis.
-/
theorem colMul_id {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {x : Pl D} (j : Fin ρ) {a : AE D}
    (h : ∀ k, colMul d.jX j a k ∈ idAt D (· = x)) : a ∈ idAt D (· = x) := by
  have h1 := mulVec_mem_idAt d.pX h j
  have h2 : (d.pX *ᵥ colMul d.jX j a) j = a * (d.pX ⬝ d.jX) j j := by
    simp only [mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rwa [h2, d.pX_jX, Matrix.one_apply_eq, mul_one] at h1

/- English proof (translation)
Use function extensionality and compare the values at `k`. Conclude with `(mul_assoc _ _ _).symm`.
-/
theorem smul_colMul {m n : ℕ} (M : Mx D m n) (i : Fin n) (s a : AE D) : s • colMul M i a = colMul M i (s * a) := by
  funext k; exact (mul_assoc _ _ _).symm

/- English proof (translation)
Introduce `i j hij s hs` and use `by have he := idem_mem_intAt (D := D) (· = x) rw [hψ s hs] constructor · intro H have := H _ ((hL j _ (Ideal.mul_mem_left _ (b j : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left])) rw [hL i _ (Ideal.mul_mem_right _ _ hs), hb i j hij, mul_inv, Units.val_mul] at this convert thi …`.
-/
theorem prim_of {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {x : Pl D}
    {cc : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ} (hb : ∀ i j : Fin ρ, j.1 = i.1 + 1 → b i = cc * b j)
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x))
    (hL : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔
      (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) : PrimAt ψ d L x := fun i j hij s hs => by
  have he := idem_mem_intAt (D := D) (· = x)
  rw [hψ s hs]
  constructor
  · intro H
    have := H _ ((hL j _ (Ideal.mul_mem_left _ (b j : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    rw [hL i _ (Ideal.mul_mem_right _ _ hs), hb i j hij, mul_inv, Units.val_mul] at this
    convert this using 1
    have e := (b j).inv_mul
    linear_combination (-((cc⁻¹ : (AE D)ˣ) : AE D)) * (mem_idAt_iff _ s).1 hs -
      (((cc⁻¹ : (AE D)ˣ) : AE D) * s * idem D (· = x)) * e
  · intro H a ha
    have := int_mul H ((hL j a (colMul_id d j (latV_idAt ha))).1 ha)
    rw [hL i _ (Ideal.mul_mem_right _ _ hs), hb i j hij, mul_inv, Units.val_mul]
    convert this using 1
    ring

/- English proof (translation)
Introduce `i a ha` and use `by rw [hα, smul_colMul, xZero, hV i a ha, hW i _ (Ideal.mul_mem_left _ _ ha), hb, mul_inv, Units.val_mul, mul_assoc, mul_left_comm]`.
-/
theorem cols_bf {V V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (d' : HypDec W W₀ ρ) {LV : Lat V} {LW : Lat W} {x : Pl D}
    {α : (AE D)ˣ} {b b' : Fin ρ → (AE D)ˣ} (hb : ∀ i, b i = α * b' i)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hV : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV V LV (· = x) ↔
      (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d'.jX i a ∈ latV W LW (· = x) ↔
      (((b' i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) : ColsAt d (xZero d') LV LW x := fun i a ha => by
  rw [hα, smul_colMul, xZero, hV i a ha, hW i _ (Ideal.mul_mem_left _ _ ha), hb, mul_inv, Units.val_mul, mul_assoc,
    mul_left_comm]

/- English proof (translation)
Introduce `i a ha` and use `by rw [hα, smul_colMul, hV i a ha] refine Fin.lastCases ?_ (fun i => ?_) i · have e : ∀ t : AE D, colMul (xLast d' z) (Fin.last σ) t = d'.j0 *ᵥ (t • ratV z) := fun t => by funext k simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul] …`.
-/
theorem cols_fb {V V₀ W W₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (d' : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    {LV : Lat V} {LW : Lat W} {LW₀ : Lat W₀} {x : Pl D} {α m : (AE D)ˣ} {b : Fin (σ + 1) → (AE D)ˣ} {b' : Fin σ → (AE D)ˣ}
    (hb : ∀ i, b i.castSucc = α * b' i) (hl : b (Fin.last σ) = α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hV : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV V LV (· = x) ↔
      (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d'.jX i a ∈ latV W LW (· = x) ↔
      (((b' i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hmono : MonoAt d' LW LW₀ x)
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV W₀ LW₀ (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ColsAt d (xLast d' z) LV LW x := fun i a ha => by
  rw [hα, smul_colMul, hV i a ha]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have e : ∀ t : AE D, colMul (xLast d' z) (Fin.last σ) t = d'.j0 *ᵥ (t • ratV z) := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e0 : ∀ (M : Mx D W.rank σ) i, colMul M i 0 = 0 := fun M i => funext fun k => zero_mul _
    rw [e, hmono, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, d'.pX_j0, d'.pY_j0, d'.p0_j0, zero_mulVec, one_mulVec,
      hz _ (Ideal.mul_mem_left _ _ ha), hl, mul_inv, Units.val_mul, mul_assoc, mul_left_comm]
    simp only [Pi.zero_apply, e0, zero_mem, implies_true, true_and]
  · have e : ∀ t : AE D, colMul (xLast d' z) i.castSucc t = colMul d'.jX i t := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_castSucc]
    rw [e, hW i _ (Ideal.mul_mem_left _ _ ha), hb, mul_inv, Units.val_mul, mul_assoc, mul_left_comm]

end GlobalTheory.GoodPos

end
