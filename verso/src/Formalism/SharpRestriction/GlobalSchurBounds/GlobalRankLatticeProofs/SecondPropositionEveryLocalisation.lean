import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition

namespace SlopeTestRemainingChoices

/- English proof (translation)
The claim follows from `(hostGroup e).2.2.2.2.2.2.2.1`.
-/
theorem ord_five (e : ℕ) : orderOf (hcl e (u5 (e + 2))) = 2 ^ e :=
  (hostGroup e).2.2.2.2.2.2.2.1

/- English proof (translation)
The claim follows from `(hostGroup e).2.2.2.2.2.2.1`.
-/
theorem card_HGrp (e : ℕ) : Nat.card (HGrp e) = 2 ^ e :=
  (hostGroup e).2.2.2.2.2.2.1

/- English proof (translation)
Unfold `iotaH`. Establish `h` using `pow_mod_orderOf (hcl e (u5 (e + 2))) (i.val + j.val)`. Rewrite `h` using `[ord_five]`. Rewrite using `[ZMod.val_add, ← pow_add]`. Conclude with `h`.
-/
theorem iotaH_add (e : ℕ) (i j : ZMod (2 ^ e)) : iotaH e (i + j) = iotaH e i * iotaH e j := by
  unfold iotaH
  have h := pow_mod_orderOf (hcl e (u5 (e + 2))) (i.val + j.val)
  rw [ord_five] at h
  rw [ZMod.val_add, ← pow_add]
  exact h

/- English proof (translation)
Unfold `iotaH`. Rewrite using `[ZMod.val_zero, pow_zero]`.
-/
theorem iotaH_zero (e : ℕ) : iotaH e 0 = 1 := by
  unfold iotaH
  rw [ZMod.val_zero, pow_zero]

/- English proof (translation)
Introduce `i j hij`. Unfold `iotaH at hij`. Rewrite `hij` using `[pow_inj_mod, ord_five e, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)]`. Conclude with `ZMod.val_injective _ hij`.
-/
theorem iotaH_injective (e : ℕ) : Function.Injective (iotaH e) := by
  intro i j hij
  unfold iotaH at hij
  rw [pow_inj_mod, ord_five e, Nat.mod_eq_of_lt (ZMod.val_lt i),
    Nat.mod_eq_of_lt (ZMod.val_lt j)] at hij
  exact ZMod.val_injective _ hij

/- English proof (translation)
Establish `: Finite (HGrp e)` using `Nat.finite_of_card_ne_zero (by rw [card_HGrp]; positivity)`. Use `(iotaH_injective e).bijective_of_nat_card_le ?_` and prove the remaining obligations. Rewrite using `[card_HGrp, Nat.card_zmod]`.
-/
theorem iotaH_bijective (e : ℕ) : Function.Bijective (iotaH e) := by
  have : Finite (HGrp e) := Nat.finite_of_card_ne_zero (by rw [card_HGrp]; positivity)
  refine (iotaH_injective e).bijective_of_nat_card_le ?_
  rw [card_HGrp, Nat.card_zmod]

/- English proof (translation)
The claim follows from `Function.rightInverse_invFun (iotaH_bijective e).2 x`.
-/
theorem iotaH_iotaHInv (e : ℕ) (x : HGrp e) : iotaH e (iotaHInv e x) = x :=
  Function.rightInverse_invFun (iotaH_bijective e).2 x

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_smul, iotaH_zero, pow_zero]`. Consider the case `succ k ih`. Rewrite using `[succ_nsmul, iotaH_add, ih]`. Conclude with `(pow_succ _ _).symm`.
-/
theorem iotaH_nsmul (e : ℕ) (k : ℕ) (i : ZMod (2 ^ e)) : iotaH e (k • i) = iotaH e i ^ k := by
  induction k with
  | zero => rw [zero_smul, iotaH_zero, pow_zero]
  | succ k ih =>
    rw [succ_nsmul, iotaH_add, ih]
    exact (pow_succ _ _).symm

def iotaHom (e : ℕ) : Multiplicative (ZMod (2 ^ e)) →* HGrp e :=
  MonoidHom.mk' (fun x => iotaH e (Multiplicative.toAdd x)) (fun _ _ => iotaH_add e _ _)

/- English proof (translation)
Establish `h` using `orderOf_injective (iotaHom e) (iotaH_injective e) (Multiplicative.ofAdd i)`. Rewrite `h` using `[orderOf_ofAdd_eq_addOrderOf]`. Conclude with `h`.
-/
theorem orderOf_iotaH (e : ℕ) (i : ZMod (2 ^ e)) : orderOf (iotaH e i) = addOrderOf i := by
  have h := orderOf_injective (iotaHom e) (iotaH_injective e) (Multiplicative.ofAdd i)
  rw [orderOf_ofAdd_eq_addOrderOf] at h
  exact h

/- English proof (translation)
Rewrite using `[ordH, ← orderOf_iotaH, iotaH_iotaHInv]`.
-/
theorem ordH_eq (e : ℕ) (x : HGrp e) : ordH (iotaHInv e x) = orderOf x := by
  rw [ordH, ← orderOf_iotaH, iotaH_iotaHInv]

/- English proof (translation)
The claim follows from `φ.cc_mul_cc`.
-/
theorem cc_mul_cc (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := φ.cc_mul_cc

section Emb

variable (D : D7)

/- English proof (translation)
The claim follows from `D.host.gal.apply_symm_apply g`.
-/
theorem galE_sigmaOf (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g :=
  D.host.gal.apply_symm_apply g

/- English proof (translation)
The claim follows from `D.host.gal.symm_apply_apply σ`.
-/
theorem sigmaOf_galE (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    D.host.sigmaOf (D.host.galE σ) = σ :=
  D.host.gal.symm_apply_apply σ

/- English proof (translation)
Establish `hCM` using `D.host.der.cmType`. Establish `hEmb` using `D.host.toHostRaw.hostEmb D.host.φ₀`. Take `⟨σ, rfl⟩` from `hEmb.2 φ`. Rewrite using `[hCM.2.2 D.host.φ₀ D.host.φ₀_mem σ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, hφ⟩`. Establish `: D.host.sigmaOf g = σ` using `hEmb.1 hφ`. Use `show D.host.galE σ ∈ D.R.Psi`. Rewrite using `[← this, galE_sigmaOf]`. Conclude with `hg`.

Introduce `hσ`. Use `⟨D.host.galE σ, hσ, ?_⟩` and prove the remaining obligations. Use `show D.host.φ₀.comp (D.host.sigmaOf _ : D.host.E →+* D.host.E) = _`. Rewrite using `[sigmaOf_galE]`.
-/
theorem mem_PhiEmb_iff (φ : D.host.E →+* ℂ) :
    φ ∈ PhiEmb D ↔ φ ∈ D.host.cmType := by
  have hCM := D.host.der.cmType
  have hEmb := D.host.toHostRaw.hostEmb D.host.φ₀
  obtain ⟨σ, rfl⟩ := hEmb.2 φ
  rw [hCM.2.2 D.host.φ₀ D.host.φ₀_mem σ]
  constructor
  · rintro ⟨g, hg, hφ⟩
    have : D.host.sigmaOf g = σ := hEmb.1 hφ
    show D.host.galE σ ∈ D.R.Psi
    rw [← this, galE_sigmaOf]
    exact hg
  · intro hσ
    refine ⟨D.host.galE σ, hσ, ?_⟩
    show D.host.φ₀.comp (D.host.sigmaOf _ : D.host.E →+* D.host.E) = _
    rw [sigmaOf_galE]

/- English proof (translation)
Use `set σ := D.host.sigmaOf g`. Establish `hb : σ (D.host.sqd) = D.host.sqd`. Use `(D.host.galE_mem_Psi_iff σ).1 ?_` and prove the remaining obligations. Rewrite using `[galE_sigmaOf]`. Conclude with `hg`.

Establish `hint : IsAlgebraic ℚ (D.host.sqd)` using `Algebra.IsAlgebraic.isAlgebraic _`. Establish `hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]`. Conclude with `hx`. Establish `hle : Algebra.adjoin ℚ {D.host.sqd} ≤ AlgHom.equalizer (σ : D.host.E →ₐ[ℚ] D.host.E) (AlgHom.id ℚ D.host.E)`.

Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Conclude with `hb`.

Conclude with `hle hx'`.
-/
theorem sigmaOf_fix_K (g : D.R.GG) (hg : g ∈ D.R.Psi) (x : D.host.E) (hx : x ∈ D.host.K) :
    D.host.sigmaOf g x = x := by
  set σ := D.host.sigmaOf g
  have hb : σ (D.host.sqd) = D.host.sqd := by
    refine (D.host.galE_mem_Psi_iff σ).1 ?_
    rw [galE_sigmaOf]
    exact hg
  have hint : IsAlgebraic ℚ (D.host.sqd) := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]
    exact hx
  have hle : Algebra.adjoin ℚ {D.host.sqd} ≤
      AlgHom.equalizer (σ : D.host.E →ₐ[ℚ] D.host.E) (AlgHom.id ℚ D.host.E) := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hb
  exact hle hx'

end Emb

end SlopeTestRemainingChoices

open SlopeTestRemainingChoices

/- English proof (translation)
Establish `hCM` using `D.host.der.cmType`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `φ`. Rewrite using `[mem_PhiEmb_iff, mem_PhiEmb_iff]`. Conclude with `hCM.1 φ`.

Introduce and unpack `φ ⟨g, hg, rfl⟩ x hx show D.host.φ₀ (D.host.sigmaOf g x) = D.host.φ₀ x`. Rewrite using `[sigmaOf_fix_K D g hg x hx]`. Introduce `τ hτ`. Conclude with `D.R.toFrame.hostPartner τ hτ`. Introduce `h t`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Simplify using `only [rho, gOf, HC.Frame.tau1, HC.Frame.tau2, HC.Frame.cc, sgc0, Prod.mk_mul_mk, one_mul, HC.Frame.iota_add]`. Use `Prod.ext ?_ (mul_comm _ _)` and prove the remaining obligations. Simplify using `only`. Evaluate the decidable proposition.

Introduce `χ`. Establish `hf : ((D.R.f : ℕ) : ℂ) = (2 * D.R.ord : ℂ)`. Simplify using `only [Ranks.f, Ranks.n]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hf]`. Conclude with `D.R.toFrame.hostCharSum.1 χ`. Introduce and unpack `⟨⟨a, b⟩, h⟩`. Apply the tactic sequence `rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>`. Apply the tactic sequence `simp [sgc0, c0, HC.Frame.chD, HC.Frame.chQ] <;> norm_num`.
-/
theorem second_proposition_every_localisation (D : D7) : Conclusion2 D := by
  have hCM := D.host.der.cmType
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    rw [mem_PhiEmb_iff, mem_PhiEmb_iff]
    exact hCM.1 φ
  · rintro φ ⟨g, hg, rfl⟩ x hx
    show D.host.φ₀ (D.host.sigmaOf g x) = D.host.φ₀ x
    rw [sigmaOf_fix_K D g hg x hx]
  · intro τ hτ
    exact D.R.toFrame.hostPartner τ hτ
  · intro h t
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [rho, gOf, HC.Frame.tau1, HC.Frame.tau2, HC.Frame.cc, sgc0, Prod.mk_mul_mk, one_mul,
        HC.Frame.iota_add]
      refine Prod.ext ?_ (mul_comm _ _)
      dsimp only
      decide
  · intro χ
    have hf : ((D.R.f : ℕ) : ℂ) = (2 * D.R.ord : ℂ) := by
      simp only [Ranks.f, Ranks.n]; push_cast; ring
    rw [hf]
    exact D.R.toFrame.hostCharSum.1 χ
  · rintro ⟨⟨a, b⟩, h⟩
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      simp [sgc0, c0, HC.Frame.chD, HC.Frame.chQ] <;> norm_num

end Formalism.MainNotions.UnusedSlot33

end
