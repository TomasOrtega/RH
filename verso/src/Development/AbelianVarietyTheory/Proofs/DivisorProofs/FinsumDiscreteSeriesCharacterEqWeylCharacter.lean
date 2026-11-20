import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PacketSumSignCastNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignEven
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.WeylPacket

/- English proof (translation)
Establish `h2 : (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)) = (Matrix.vandermonde (a ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm`. Use extensionality with `i j`. Simplify using `[Matrix.vandermonde_apply, Fin.rev_rev]`. Establish `key : ∀ f : Fin r → Fin r → ℂ, ∏ i, ∏ j ∈ Finset.Ioi i, f i j = ∏ i, ∏ j, if i < j then f i j else 1`. Introduce `f`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `j`. Simplify using the standard rewrite rules.

Establish `key2 : ∀ f : Fin r → Fin r → ℂ, ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j = ∏ i, ∏ j, if i < j then f i j else 1` using `fun f => Finset.prod_congr rfl fun i _ => Finset.prod_filter _ _`. Rewrite using `[h2, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, Formalism.PacketSums.vdm, key, key2, Finset.prod_comm]`. Use `Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_` and prove the remaining obligations. Use `Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_` and prove the remaining obligations. Simplify using `[Fin.rev_lt_rev]`.
-/
theorem det_rev_pow_eq_vdm {r : ℕ} (a : Fin r → ℂ) :
    (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)).det = Formalism.PacketSums.vdm a := by
  have h2 : (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)) =
      (Matrix.vandermonde (a ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [Matrix.vandermonde_apply, Fin.rev_rev]
  have key : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.Ioi i, f i j = ∏ i, ∏ j, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have key2 : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j = ∏ i, ∏ j, if i < j then f i j else 1 :=
    fun f => Finset.prod_congr rfl fun i _ => Finset.prod_filter _ _
  rw [h2, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, Formalism.PacketSums.vdm, key, key2, Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp [Fin.rev_lt_rev]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Fintype.prod_equiv w _ _ fun i => by simp`.
-/
theorem det_zpow_eq_sum {r : ℕ} (a : Fin r → ℂ) (m : Fin r → ℤ) :
    (Matrix.of fun i j : Fin r => a i ^ m j).det =
      ∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, a i ^ m (w⁻¹ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact Fintype.prod_equiv w _ _ fun i => by simp

end GlobalTheory.WeylPacket

open GlobalTheory.WeylPacket in

/- English proof (translation)
Introduce `n ε lam α ι _ y θ hn hα hb hθ`. Use `haveI : Fintype ι := Fintype.ofFinite ι`. Take `⟨k, hk⟩` from `id hn`. Use `set m : Fin n → ℤ := fun a => lam a + (((n - 1) / 2 : ℕ) : ℤ) with hmdef`. Establish `hk2 : (n - 1) / 2 = k` using `by omega`.

Establish `hm : ∀ a, ((fun a => (lam a : ℝ)) a) + ((n : ℝ) - 1) / 2 = (m a : ℝ)`. Introduce `a`. Establish `hn' : (n : ℝ) = 2 * k + 1` using `by exact_mod_cast hk`. Simplify using `only [hmdef, hk2, hn']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Set `WK : Subgroup (Equiv.Perm (Fin n))` to `{ carrier := {w | ε ∘ w = ε} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at *`. Use function extensionality and compare the values at `x`.

Establish `ha'` using `congrFun ha (b x)`. Establish `hb'` using `congrFun hb x`. Simplify using `only [Function.comp_apply] at ha' hb' ⊢`. Rewrite using `[Equiv.Perm.mul_apply, ha', hb']`. Use the proof step `one_mem' := by simp`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Use function extensionality and compare the values at `x`. Use `congrFun ha (a⁻¹ x)` as an intermediate fact.

Simplify using `only [Function.comp_apply] at this ⊢`. Rewrite `this` using `[show a (a⁻¹ x) = x from by simp]`. Conclude with `this.symm }`. Use `haveI : Fintype WK := Fintype.ofFinite _`. Establish `hmem : ∀ w, w ∈ WK ↔ w ∈ compactWeyl ε`.

Introduce `w`. Use `show ε ∘ w = ε ↔ _`. Simplify using `[compactWeyl]`. Establish `h1 : (1 : Equiv.Perm (Fin n)) ∈ compactWeyl ε` using `by simp [compactWeyl]`. Establish `hy : Function.Injective y`.

Introduce `q q' h`. Use `hb.1 (a₁ := (⟨1, h1⟩, q)) (a₂ := (⟨1, h1⟩, q')) (by simp [h])` as an intermediate fact. Conclude with `congrArg Prod.snd this`. Establish `hα0 : ∀ i, α i ≠ 0`. Introduce `i`.

Take `⟨⟨w, q⟩, -⟩` from `hb.2 1`. Use `hθ q (y q i)` as an intermediate fact. Rewrite `this` using `[show (y q)⁻¹ (y q i) = i from by simp]`. Rewrite using `[← this]`. Conclude with `Complex.exp_ne_zero _`.

Use `set T : Finset (Equiv.Perm (Fin n)) := Finset.univ.image y with hT`. Set `eT : ι ≃ T` to `Equiv.ofBijective (fun q => ⟨y q, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩) ⟨fun q q' h => hy (congrArg Subtype.val h), fun ⟨g, hg⟩ => by`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hg`. Conclude with `⟨q, rfl⟩⟩`. Set `e : compactWeyl ε × ι ≃ WK × T` to `Equiv.prodCongr (Equiv.subtypeEquivRight fun w => (hmem w).symm) eT`.

Establish `hbij : Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin n)))⁻¹ * (p.1 : Equiv.Perm (Fin n)))` using `(Equiv.bijective_comp e _).1 hb`. Establish `hPS` using `GlobalTheory.packetSum n WK T hbij m α hα0 hα`. Establish `hsign : (-1 : ℂ) ^ halfDim ε = 1`. Establish `hpq` using `Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : Fin n => ε a = true)`. Simplify using `only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpq`.

Use `GlobalTheory.signEven _ _ (by rw [hpq]; exact hn)` as an intermediate fact. Rewrite using `[halfDim]`. Conclude with `this` after adjusting the coercions. Establish `hterm : ∀ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = Formalism.PacketSums.numK WK m (fun i => α ((y q)⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α ((y q)⁻¹ i))`. Introduce `q`.

Rewrite using `[dsChar_eq ε hm (θ q), hsign, one_mul]`. Simplify using `only [hθ q]`. Use `congr 1`. Rewrite using `[Formalism.PacketSums.numK, Finset.sum_subtype (compactWeyl ε) (fun w => (hmem w).symm)]`. Both sides reduce to the same expression.

Rewrite using `[Formalism.PacketSums.vdm]`. Conclude with `Finset.prod_congr rfl fun i _ => Finset.prod_congr (by ext j; simp) fun _ _ => rfl`. Establish `hexp : ∀ j : Fin n, hiWt lam j + ((j.rev : ℕ) : ℤ) = m j`. Introduce `j`. Use `j.isLt` as an intermediate fact.

Simplify using `only [hiWt, hmdef, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => hterm q, ← Finset.sum_image (f := fun g : Equiv.Perm (Fin n) => Formalism.PacketSums.numK WK m (fun i => α (g⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (g⁻¹ i))) (fun q _ q' _ h => hy h), ← hT, hPS, glChar, det_rev_pow …`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `only [Matrix.of_apply, hexp j]`.
-/
theorem GlobalTheory.dsChar_finsum_eq_glChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  intro n ε lam α ι _ y θ hn hα hb hθ
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := id hn
  set m : Fin n → ℤ := fun a => lam a + (((n - 1) / 2 : ℕ) : ℤ) with hmdef
  have hk2 : (n - 1) / 2 = k := by omega
  have hm : ∀ a, ((fun a => (lam a : ℝ)) a) + ((n : ℝ) - 1) / 2 = (m a : ℝ) := by
    intro a
    have hn' : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    simp only [hmdef, hk2, hn']
    push_cast
    ring
  let WK : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {w | ε ∘ w = ε}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        funext x
        have ha' := congrFun ha (b x)
        have hb' := congrFun hb x
        simp only [Function.comp_apply] at ha' hb' ⊢
        rw [Equiv.Perm.mul_apply, ha', hb']
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        funext x
        have := congrFun ha (a⁻¹ x)
        simp only [Function.comp_apply] at this ⊢
        rw [show a (a⁻¹ x) = x from by simp] at this
        exact this.symm }
  haveI : Fintype WK := Fintype.ofFinite _
  have hmem : ∀ w, w ∈ WK ↔ w ∈ compactWeyl ε := by
    intro w
    show ε ∘ w = ε ↔ _
    simp [compactWeyl]
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ compactWeyl ε := by simp [compactWeyl]
  have hy : Function.Injective y := by
    intro q q' h
    have := hb.1 (a₁ := (⟨1, h1⟩, q)) (a₂ := (⟨1, h1⟩, q')) (by simp [h])
    exact congrArg Prod.snd this
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i
    obtain ⟨⟨w, q⟩, -⟩ := hb.2 1
    have := hθ q (y q i)
    rw [show (y q)⁻¹ (y q i) = i from by simp] at this
    rw [← this]
    exact Complex.exp_ne_zero _
  set T : Finset (Equiv.Perm (Fin n)) := Finset.univ.image y with hT
  let eT : ι ≃ T := Equiv.ofBijective (fun q => ⟨y q, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩)
    ⟨fun q q' h => hy (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
      exact ⟨q, rfl⟩⟩
  let e : compactWeyl ε × ι ≃ WK × T :=
    Equiv.prodCongr (Equiv.subtypeEquivRight fun w => (hmem w).symm) eT
  have hbij : Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin n)))⁻¹ * (p.1 : Equiv.Perm (Fin n))) :=
    (Equiv.bijective_comp e _).1 hb
  have hPS := GlobalTheory.packetSum n WK T hbij m α hα0 hα
  have hsign : (-1 : ℂ) ^ halfDim ε = 1 := by
    have hpq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : Fin n => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpq
    have := GlobalTheory.signEven _ _ (by rw [hpq]; exact hn)
    rw [halfDim]
    exact_mod_cast this
  have hterm : ∀ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) =
      Formalism.PacketSums.numK WK m (fun i => α ((y q)⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α ((y q)⁻¹ i)) := by
    intro q
    rw [dsChar_eq ε hm (θ q), hsign, one_mul]
    simp only [hθ q]
    congr 1
    · rw [Formalism.PacketSums.numK, Finset.sum_subtype (compactWeyl ε) (fun w => (hmem w).symm)]
      rfl
    · rw [Formalism.PacketSums.vdm]
      exact Finset.prod_congr rfl fun i _ => Finset.prod_congr (by ext j; simp) fun _ _ => rfl
  have hexp : ∀ j : Fin n, hiWt lam j + ((j.rev : ℕ) : ℤ) = m j := by
    intro j
    have := j.isLt
    simp only [hiWt, hmdef, Fin.val_rev]
    omega
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => hterm q,
    ← Finset.sum_image (f := fun g : Equiv.Perm (Fin n) => Formalism.PacketSums.numK WK m (fun i => α (g⁻¹ i)) /
      Formalism.PacketSums.vdm (fun i => α (g⁻¹ i))) (fun q _ q' _ h => hy h), ← hT, hPS, glChar, det_rev_pow_eq_vdm,
    ← det_zpow_eq_sum]
  congr 2
  ext i j
  simp only [Matrix.of_apply, hexp j]
