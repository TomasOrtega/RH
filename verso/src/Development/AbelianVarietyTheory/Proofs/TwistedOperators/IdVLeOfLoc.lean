import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise

noncomputable section

namespace GlobalTheory.StairLine

open GlobalTheory.SeeSaw (FI idV dI)

variable {D : D7}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef`. Establish `hσ : ∀ e, σ (σ e) = e` using `fun e => star_star e`. Establish `hG : Formalism.UG.cT σ B.gram = B.gram` using `by funext i j; exact B.herm.eq (B.frame j) (B.frame i)`. Establish `eT : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) (Y : Matrix (Fin n) (Fin p) D.host.E), Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X` using `by intros; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]`. Establish `eTT : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X` using `by intros; ext i j; simp [Formalism.UG.cT, hσ]`.

Establish `hperp : Formalism.UG.cT σ d.a * B.gram * frameMat B A d.ι = 0`. Establish `h1` using `congrArg (Formalism.UG.cT σ) d.perp`. Rewrite `h1` using `[eT, eT, eTT, hG, ← Matrix.mul_assoc]`. Rewrite using `[h1]`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT]`. Set `P` to `Formalism.UG.cT σ d.a * B.gram`. Set `r : Fin B.rank → D.host.E` to `x⁻¹ • P q.rev`. Establish `hrow : ∀ {n : ℕ} (N : Matrix (Fin B.rank) (Fin n) D.host.E), r ᵥ* N = x⁻¹ • (P * N) q.rev` using `by intros; funext j; simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]`. Establish `hrM : ∀ y, r ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0`.

Introduce `y`. Rewrite using `[Matrix.dotProduct_mulVec, hrow, show P * frameMat B A d.ι = 0 from hperp, show ((0 : Matrix (Fin c) (Fin A.rank) D.host.E) q.rev) = 0 from rfl, smul_zero, zero_dotProduct]`. Establish `hgram : P * d.a = antiDiagonalSignGramMatrix c ε` using `d.gram`. Establish `hra : ∀ u : Fin c → D.host.E, r ⬝ᵥ (d.a *ᵥ u) = x⁻¹ * u q`. Introduce `u`.

Rewrite using `[Matrix.dotProduct_mulVec, hrow, hgram]`. Simplify using `only [dotProduct, Pi.smul_apply, smul_eq_mul, antiDiagonalSignGramMatrix]`. Rewrite using `[Finset.sum_eq_single q]`. Establish `h1 : q.rev.1 + q.1 + 1 = c` using `by rw [Fin.val_rev]; omega`. Establish `h2 : q.rev ≠ q` using `by intro h; rw [Fin.ext_iff, Fin.val_rev] at h; omega`.

Rewrite using `[if_pos h1, if_neg h2, mul_one]`. Introduce `p _ hp`. Establish `: ¬ (q.rev.1 + p.1 + 1 = c)`. Introduce `h`. Apply `hp` to reduce the goal to its premises.

Rewrite using `[Fin.ext_iff]`. Rewrite `h` using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg this, mul_zero, zero_mul]`. Simplify using the standard rewrite rules.

Establish `hlat : ∀ y ∈ d.lat Λ 𝔟, r ⬝ᵥ y ∈ FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q`. Introduce and unpack `_ ⟨y, -, u, hu, rfl⟩`. Rewrite using `[dotProduct_add, hrM, zero_add, hra]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hu q)`. Establish `hcol : r ⬝ᵥ (fun k => x * d.a k q) = 1`.

Establish `e : (fun k => x * d.a k q) = d.a *ᵥ Pi.single q x`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`. Rewrite using `[e, hra, Pi.single_eq_same, inv_mul_cancel₀ hx]`. Prove the components needed by the constructor for the conclusion.

Introduce `hmem`. Establish `hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), ∑ k, incA D (r k) * Y k ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v`. Introduce `Y hY`. Proceed by induction on `hY using AddSubgroup.closure_induction with`. Consider the case `mem Y hY`.

Take `⟨α, h1, h2, b, hb, y, hy, rfl⟩` from `hY`. Rewrite `hb` using `[Set.mem_singleton_iff]`. Substitute `hb` using the available equality. Use `AddSubgroup.subset_closure ⟨α, h1, h2, _, hlat y hy, ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul, ← TensorProduct.tmul_sum, dotProduct]`.

Consider the case `zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]`. Conclude with `zero_mem _`. Consider the case `add Y Z _ _ hY hZ`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Conclude with `add_mem hY hZ`.

Consider the case `neg Y _ hY`. Simplify using `only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]`. Conclude with `neg_mem hY`. Establish `h` using `hΦ _ hmem`. Establish `e : ∑ k, incA D (r k) * (a * incA D (x * d.a k q)) = a`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [dotProduct, map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = a := by rw [hcol, map_one, mul_one]`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Introduce `ha`. Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨α, h1, h2, b, hb, rfl⟩` from `hz`.

Take `⟨b', hb', rfl⟩` from `(FractionalIdeal.mem_singleton_mul).1 hb`. Use `AddSubgroup.subset_closure ⟨α, h1, h2, 1, rfl, d.a *ᵥ Pi.single q b', ?_, ?_⟩` and prove the remaining obligations. Use `⟨0, Λ.zero_mem, Pi.single q b', fun p => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hp : p = q`. Substitute `hp` using the available equality.

Simplify using `using hb'`. Rewrite using `[Pi.single_eq_of_ne hp]`. Conclude with `(𝔟 p).zero_mem`. Use function extensionality and compare the values at `k`. Establish `e1 : x * d.a k q * (x⁻¹ * b') = 1 * (d.a *ᵥ Pi.single q b') k`.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x⁻¹ * b')), GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, e1]`. Consider the case `zero`. Establish `e0 : (fun k => (0 : AE D) * incA D (x * d.a k q)) = 0` using `by funext k; exact zero_mul _`.

Rewrite using `[e0]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `: (fun k => (y + z) * incA D (x * d.a k q)) = (fun k => y * incA D (x * d.a k q)) + fun k => z * incA D (x * d.a k q)`. Use function extensionality and compare the values at `k`.

Simplify using `[add_mul]`. Rewrite using `[this]`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy`. Establish `: (fun k => -y * incA D (x * d.a k q)) = -fun k => y * incA D (x * d.a k q)`.

Use function extensionality and compare the values at `k`. Simplify using `[neg_mul]`. Rewrite using `[this]`. Conclude with `neg_mem hy`.
-/
theorem line_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FI D) (q : Fin c) (hq : 2 * q.1 + 1 ≠ c)
    {x : D.host.E} (hx : x ≠ 0) (v : GlobalTheory.FinPl.Pl D) (a : AE D) :
    (fun k => a * incA D (x * d.a k q)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔
      a ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef
  have hσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have hG : Formalism.UG.cT σ B.gram = B.gram := by funext i j; exact B.herm.eq (B.frame j) (B.frame i)
  have eT : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) (Y : Matrix (Fin n) (Fin p) D.host.E),
      Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
    intros; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have eTT : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intros; ext i j; simp [Formalism.UG.cT, hσ]
  have hperp : Formalism.UG.cT σ d.a * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg (Formalism.UG.cT σ) d.perp
    rw [eT, eT, eTT, hG, ← Matrix.mul_assoc] at h1
    rw [h1]; ext i j; simp [Formalism.UG.cT]
  let P := Formalism.UG.cT σ d.a * B.gram
  let r : Fin B.rank → D.host.E := x⁻¹ • P q.rev
  have hrow : ∀ {n : ℕ} (N : Matrix (Fin B.rank) (Fin n) D.host.E), r ᵥ* N = x⁻¹ • (P * N) q.rev := by
    intros; funext j; simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have hrM : ∀ y, r ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hrow, show P * frameMat B A d.ι = 0 from hperp,
      show ((0 : Matrix (Fin c) (Fin A.rank) D.host.E) q.rev) = 0 from rfl, smul_zero, zero_dotProduct]
  have hgram : P * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have hra : ∀ u : Fin c → D.host.E, r ⬝ᵥ (d.a *ᵥ u) = x⁻¹ * u q := by
    intro u
    rw [Matrix.dotProduct_mulVec, hrow, hgram]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, antiDiagonalSignGramMatrix]
    rw [Finset.sum_eq_single q]
    · have h1 : q.rev.1 + q.1 + 1 = c := by rw [Fin.val_rev]; omega
      have h2 : q.rev ≠ q := by intro h; rw [Fin.ext_iff, Fin.val_rev] at h; omega
      rw [if_pos h1, if_neg h2, mul_one]
    · intro p _ hp
      have : ¬ (q.rev.1 + p.1 + 1 = c) := by
        intro h; apply hp; rw [Fin.ext_iff]; rw [Fin.val_rev] at h; omega
      rw [if_neg this, mul_zero, zero_mul]
    · simp
  have hlat : ∀ y ∈ d.lat Λ 𝔟, r ⬝ᵥ y ∈ FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q := by
    rintro _ ⟨y, -, u, hu, rfl⟩
    rw [dotProduct_add, hrM, zero_add, hra]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hu q)
  have hcol : r ⬝ᵥ (fun k => x * d.a k q) = 1 := by
    have e : (fun k => x * d.a k q) = d.a *ᵥ Pi.single q x := by
      funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [e, hra, Pi.single_eq_same, inv_mul_cancel₀ hx]
  constructor
  · intro hmem
    have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), ∑ k, incA D (r k) * Y k ∈
        idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
      intro Y hY
      induction hY using AddSubgroup.closure_induction with
      | mem Y hY =>
        obtain ⟨α, h1, h2, b, hb, y, hy, rfl⟩ := hY
        rw [Set.mem_singleton_iff] at hb
        subst hb
        refine AddSubgroup.subset_closure ⟨α, h1, h2, _, hlat y hy, ?_⟩
        simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul, ← TensorProduct.tmul_sum, dotProduct]
      | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
      | add Y Z _ _ hY hZ =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hY hZ
      | neg Y _ hY =>
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; exact neg_mem hY
    have h := hΦ _ hmem
    have e : ∑ k, incA D (r k) * (a * incA D (x * d.a k q)) = a := by
      calc _ = a * incA D (r ⬝ᵥ (fun k => x * d.a k q)) := by
            simp only [dotProduct, map_sum, map_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = a := by rw [hcol, map_one, mul_one]
    rwa [e] at h
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, h1, h2, b, hb, rfl⟩ := hz
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hb
      refine AddSubgroup.subset_closure ⟨α, h1, h2, 1, rfl, d.a *ᵥ Pi.single q b', ?_, ?_⟩
      · refine ⟨0, Λ.zero_mem, Pi.single q b', fun p => ?_, by simp⟩
        by_cases hp : p = q
        · subst hp; simpa using hb'
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        have e1 : x * d.a k q * (x⁻¹ * b') = 1 * (d.a *ᵥ Pi.single q b') k := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          field_simp
        rw [mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x⁻¹ * b')), GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, e1]
    | zero =>
      have e0 : (fun k => (0 : AE D) * incA D (x * d.a k q)) = 0 := by funext k; exact zero_mul _
      rw [e0]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun k => (y + z) * incA D (x * d.a k q)) =
          (fun k => y * incA D (x * d.a k q)) + fun k => z * incA D (x * d.a k q) := by
        funext k; simp [add_mul]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun k => -y * incA D (x * d.a k q)) = -fun k => y * incA D (x * d.a k q) := by
        funext k; simp [neg_mul]
      rw [this]; exact neg_mem hy

/- English proof (translation)
Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, h1, h2, a, ha, rfl⟩`. Take `⟨t, ht, htb⟩` from `h a ha`. Take `⟨g1, g2⟩` from `GlobalTheory.IdVGen.smul_inv_mem ht h1 h2`. Conclude with `AddSubgroup.subset_closure ⟨_, g1, g2, _, htb, GlobalTheory.IdVGen.tmul_eq ht α a⟩`.
-/
theorem idV_le_of_loc {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : ∀ z ∈ 𝔞, ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t * z ∈ 𝔟) : idV 𝔞 v ≤ idV 𝔟 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨t, ht, htb⟩ := h a ha
  obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
  exact AddSubgroup.subset_closure ⟨_, g1, g2, _, htb, GlobalTheory.IdVGen.tmul_eq ht α a⟩

/- English proof (translation)
Establish `hu : ∀ u ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ u.asIdeal ∧ t ∉ v.asIdeal`. Introduce `u hu`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `e : u = v` using `IsDedekindDomain.HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hcon)`.

Conclude with `hv (e ▸ hu)`. Use `choose! tu htu htv using hu`. Set `t : 𝓞 D.host.F` to `∏ u ∈ P.S0, tu u ^ P.depth sc u`. Establish `htv' : t ∉ v.asIdeal`. Introduce `hmem`.

Take `⟨u, hu, hmem'⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem`. Conclude with `htv u hu (v.isPrime.mem_of_pow_mem _ hmem')`. Establish `hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc`. Simplify using `only [t, map_prod, map_pow, Places.modul]`. Use `Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow ?_ _` and prove the remaining obligations.

Establish `e` using `P.under_w hu`. Establish `: tu u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal` using `by rw [e]; exact htu u hu`. Conclude with `this`. Establish `hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `(D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2`. Establish `hbar : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modulBar sc`. Rewrite using `[← hfix]`. Conclude with `Ideal.smul_mem_pointwise_smul _ _ _ hmod`. Use `⟨t * t, v.isPrime.mul_notMem htv' htv', ?_⟩` and prove the remaining obligations.

Use `(FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_mul hmod hbar, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_modul {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t ∈
      (((P.modul sc * P.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ u.asIdeal ∧ t ∉ v.asIdeal := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have e : u = v := IsDedekindDomain.HeightOneSpectrum.ext
      (u.isMaximal.eq_of_le v.isPrime.ne_top hcon)
    exact hv (e ▸ hu)
  choose! tu htu htv using hu
  let t : 𝓞 D.host.F := ∏ u ∈ P.S0, tu u ^ P.depth sc u
  have htv' : t ∉ v.asIdeal := by
    intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact htv u hu (v.isPrime.mem_of_pow_mem _ hmem')
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
    simp only [t, map_prod, map_pow, Places.modul]
    refine Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow ?_ _
    have e := P.under_w hu
    have : tu u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [e]; exact htu u hu
    exact this
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t := by
    apply Subtype.ext
    exact (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  have hbar : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modulBar sc := by
    rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hmod
  refine ⟨t * t, v.isPrime.mul_notMem htv' htv', ?_⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_mul hmod hbar, ?_⟩
  rw [← map_mul]
  rfl

end GlobalTheory.StairLine
