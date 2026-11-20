import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GlobalTheory.MomDual

variable {g : ℕ}

/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hf Hm (z + z') w = hf Hm z w + hf Hm z' w := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hf_sub_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hf Hm (z - z') w = hf Hm z w - hf Hm z' w := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hf Hm (c • z) w = c * hf Hm z w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[hf]`.
-/
theorem hf_zero_left (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hf Hm 0 w = 0 := by
  simp [hf]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [hf_zero_left]`. Consider the case `insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]`.
-/
theorem hf_sum_left (Hm : Matrix (Fin g) (Fin g) ℂ) {ι : Type*} (t : Finset ι) (c : ι → ℂ) (v : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ k ∈ t, c k • v k) w = ∑ k ∈ t, c k * hf Hm (v k) w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hf Hm z (c • w) = conj c * hf Hm z w := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h : Hm j i = conj (Hm i j)`. Use `congrFun (congrFun hH j) i` as an intermediate fact.

Simplify `this.symm` using `[Matrix.conjTranspose_apply]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hf Hm w z = conj (hf Hm z w) := by
  simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : Hm j i = conj (Hm i j) := by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  rw [h]; ring

/- English proof (translation)
Establish `hx : star z ≠ 0` using `by simpa using hz`. Establish `h` using `hH.dotProduct_mulVec_pos hx`. Establish `e : dotProduct (star (star z)) (Hm.mulVec (star z)) = hf Hm z z`. Simplify using `[hf, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Rewrite `h` using `[e]`.

Conclude with `h.ne'`.
-/
theorem hf_self_ne {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.PosDef) {z : Fin g → ℂ} (hz : z ≠ 0) : hf Hm z z ≠ 0 := by
  have hx : star z ≠ 0 := by simpa using hz
  have h := hH.dotProduct_mulVec_pos hx
  have e : dotProduct (star (star z)) (Hm.mulVec (star z)) = hf Hm z z := by
    simp [hf, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  exact h.ne'

/- English proof (translation)
Introduce `q _ g S r b hS hb`. Take `⟨hdp, -, hpos, hdisc, hspan, hw0, -, hdual⟩` from `hS`. Take `⟨hbL, hgen, hind⟩` from `hb`. Take `⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt S.d / 2` from `⟨_, rfl⟩`. Establish `hρ0 : ρ ≠ 0`.

Establish `: (0:ℝ) < S.d` using `by exact_mod_cast hdp.pos`. Rewrite using `[hρ]`. Check the signs of the components of the expression. Establish `hρc : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ0`. Establish `hbeta : ∀ z w, beta S.d S.Hm z w = (ρ : ℂ) * hf S.Hm z w` using `fun z w => by rw [hρ]; rfl`.

Establish `hw0im : (w0 S.d).im = ρ` using `by simp [w0, rtd, hρ]`. Establish `hOKim : ∀ c ∈ OK S.d, ∃ v : ℤ, c.im = v * ρ`. Introduce and unpack `c ⟨u, v, rfl⟩; exact ⟨v, by simp [hw0im]⟩`. Establish `hqs : ∀ s : ℕ, Nat.Coprime s q → s ≠ 0`. Introduce and unpack `s hs rfl`.

Conclude with `(Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hs)`. Establish `hmemspan : ∀ x ∈ S.La, ∃ μ : Fin r → ℂ, x = ∑ i, μ i • b i`. Introduce `x hx`. Take `⟨s, hs, c, -, he⟩` from `hgen x hx`. Establish `hs0 : (s : ℂ) ≠ 0` using `by exact_mod_cast hqs s hs`.

Use `⟨fun i => (s : ℂ)⁻¹ * c i, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[← smul_smul]`. Rewrite using `[← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Establish `htop : (⊤ : Submodule ℂ (Fin g → ℂ)) ≤ Submodule.span ℂ (Set.range b)`. Establish `h1 : Submodule.span ℝ (S.La : Set (Fin g → ℂ)) ≤ (Submodule.span ℂ (Set.range b)).restrictScalars ℝ`.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨μ, rfl⟩` from `hmemspan x hx`. Use `show _ ∈ Submodule.span ℂ (Set.range b)`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Introduce `x _`. Establish `: x ∈ Submodule.span ℝ (S.La : Set (Fin g → ℂ))` using `by rw [hspan]; trivial`. Conclude with `h1 this`. Use `haveI : DiscreteTopology S.La := hdisc`. Use `haveI : IsZLattice ℝ S.La := ⟨hspan⟩`.

Establish `hrk : Module.finrank ℤ S.La = 2 * g`. Rewrite using `[ZLattice.rank ℝ S.La]`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree. Establish `hli2 : LinearIndependent ℤ (fun p : Fin r ⊕ Fin r => (⟨Sum.elim (fun i => b i) (fun i => w0 S.d • b i) p, by rcases p with i | i; exacts [hbL i, hw0 _ (hbL i)]⟩ : S.La))`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `n hn`. Establish `hn'` using `congrArg Subtype.val hn`. Simplify using `only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, Submodule.coe_zero] at hn'`. Establish `key : ∑ i, ((n (Sum.inl i) : ℂ) + (n (Sum.inr i) : ℂ) * w0 S.d) • b i = 0`.

Rewrite using `[← hn']`. Simplify using `only [add_smul, mul_smul, Finset.sum_add_distrib, Int.cast_smul_eq_zsmul]`. Establish `hc` using `hind _ (fun i => ⟨n (Sum.inl i), n (Sum.inr i), rfl⟩) key`. Establish `hm : ∀ i, n (Sum.inr i) = 0` using `fun i => by`. Use `congrArg Complex.im (hc i)` as an intermediate fact.

Simplify `this` using `[hw0im, hρ0]`. Establish `hl : ∀ i, n (Sum.inl i) = 0` using `fun i => by`. Use `hc i` as an intermediate fact. Simplify using `only [hm i, Int.cast_zero, zero_mul, add_zero] at this`. Conclude with `this` after adjusting the coercions.

Introduce and unpack `(i | i)`. Use `exacts [hl i, hm i]`. Establish `hrg : r ≤ g`. Use `hli2.fintype_card_le_finrank` as an intermediate fact. Simplify using `only [Fintype.card_sum, Fintype.card_fin, hrk] at this`.

Use linear arithmetic over natural numbers and integers. Establish `hlin : LinearIndependent ℂ b` using `linearIndependent_of_top_le_span_of_card_le_finrank htop (by simpa using hrg)`. Establish `hconj` using `hf_conj hpos.isHermitian`. Establish `L0 : ∀ μ : Fin r → ℂ, (∀ i, hf S.Hm (∑ k, μ k • b k) (b i) = 0) → ∑ k, μ k • b k = 0`. Introduce `μ h`.

Assume the negation of the conclusion as `hne`. Apply `hf_self_ne hpos hne` to reduce the goal to its premises. Rewrite using `[hf_sum_left]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hconj, h k, map_zero, mul_zero]`.

Take `⟨A, hAdef⟩ : ∃ A : Matrix (Fin r) (Fin r) ℂ, A = fun i j => hf S.Hm (b i) (b j)` from `⟨_, rfl⟩`. Establish `hvm : ∀ w : Fin r → ℂ, ∀ i, Matrix.vecMul w A i = hf S.Hm (∑ k, w k • b k) (b i)`. Introduce `w i`. Rewrite using `[hf_sum_left, hAdef]`. Both sides reduce to the same expression.

Establish `hA : IsUnit A`. Rewrite using `[← Matrix.vecMul_injective_iff_isUnit]`. Introduce `u v huv`. Establish `h0 : ∑ k, (u - v) k • b k = 0`. Apply `L0` to reduce the goal to its premises.

Introduce `i`. Establish `huv' : Matrix.vecMul u A = Matrix.vecMul v A` using `huv`. Rewrite using `[← hvm, Matrix.sub_vecMul, huv', sub_self]`. Both sides reduce to the same expression. Use `Fintype.linearIndependent_iff.mp hlin (u - v) h0` as an intermediate fact.

Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.mp (this i)`. Establish `hinv : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)`. Take `⟨bs, hbsdef⟩ : ∃ bs : Fin r → Fin g → ℂ, bs = fun j => ∑ k, ((ρ : ℂ)⁻¹ * A⁻¹ j k) • b k` from `⟨_, rfl⟩`. Establish `hbs : ∀ j i, (ρ : ℂ) * hf S.Hm (bs j) (b i) = if j = i then 1 else 0`.

Introduce `j i`. Rewrite using `[hbsdef]`. Simplify using `only [hf_sum_left]`. Use `congrFun (congrFun hinv j) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Rewrite using `[← this, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρc, one_mul, hAdef]`. Establish `hbs2 : ∀ j i, hf S.Hm (bs j) (b i) = (ρ : ℂ)⁻¹ * (if j = i then 1 else 0)`. Introduce `j i`.

Rewrite using `[← hbs j i, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]`. Establish `hbs' : ∀ j i, (ρ : ℂ) * hf S.Hm (b i) (bs j) = if j = i then 1 else 0`. Introduce `j i`. Rewrite using `[hconj, ← Complex.conj_ofReal ρ, ← map_mul, hbs]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hOKint : ∀ (c : Fin r → ℂ), (∀ i, c i ∈ OK S.d) → ∀ j, ∃ z : ℤ, (hf S.Hm (∑ i, c i • b i) (bs j)).im = z`. Introduce `c hc j`. Establish `e : (ρ : ℂ) * hf S.Hm (∑ i, c i • b i) (bs j) = c j`. Rewrite using `[hf_sum_left, Finset.mul_sum]`. Repeatedly rewrite using `[mul_left_comm (ρ : ℂ), hbs']`.

Simplify using the standard rewrite rules. Take `⟨v, hv⟩` from `hOKim _ (hc j)`. Use `⟨v, ?_⟩` and prove the remaining obligations. Establish `h2 : hf S.Hm (∑ i, c i • b i) (bs j) = c j / (ρ : ℂ)`. Rewrite using `[← e]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h2, Complex.div_ofReal_im, hv]`. Clear the denominators using the available nonvanishing facts. Establish `okAdd : ∀ a a', a ∈ OK S.d → a' ∈ OK S.d → a + a' ∈ OK S.d`. Introduce and unpack `_ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩; exact ⟨u + u', v + v', by push_cast; ring⟩`.

Establish `okMul : ∀ (n : ℤ) a, a ∈ OK S.d → (n : ℂ) * a ∈ OK S.d`. Introduce and unpack `n _ ⟨u, v, rfl⟩; exact ⟨n * u, n * v, by push_cast; ring⟩`. Establish `ok0 : (0 : ℂ) ∈ OK S.d` using `⟨0, 0, by simp⟩`. Set `P : (Fin g → ℂ) → Prop` to `fun y => ∃ c : Fin r → ℂ, (∀ i, c i ∈ OK S.d) ∧ y = ∑ i, c i • b i`. Establish `Padd : ∀ y y', P y → P y' → P (y + y')`.

Introduce and unpack `_ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩`. Conclude with `⟨c + c', fun i => okAdd _ _ (hc i) (hc' i), by simp [add_smul, Finset.sum_add_distrib]⟩`. Establish `P0 : P 0` using `⟨0, fun _ => ok0, by simp⟩`. Establish `Pz : ∀ (n : ℤ) y, P y → P ((n : ℂ) • y)`. Introduce and unpack `n _ ⟨c, hc, rfl⟩`.

Conclude with `⟨fun i => (n : ℂ) * c i, fun i => okMul n _ (hc i), by rw [Finset.smul_sum]; simp [smul_smul]⟩`. Use `haveI : Module.Finite ℤ S.La := ZLattice.module_finite ℝ S.La`. Use `haveI : Module.Free ℤ S.La := ZLattice.module_free ℝ S.La`. Take `⟨ι, _, ⟨eB⟩⟩ : ∃ (ι : Type) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ S.La)` from `⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ S.La⟩⟩`. Use `choose sI hsI cI hcI heqI using fun k : ι => hgen _ (eB k).2`.

Take `⟨s, hs⟩ : ∃ s : ℕ, s = ∏ k, sI k` from `⟨_, rfl⟩`. Establish `hsq : Nat.Coprime s q` using `hs ▸ Nat.Coprime.prod_left fun k _ => hsI k`. Establish `hsk : ∀ k, (s : ℂ) • ((eB k : S.La) : Fin g → ℂ) = (((∏ l ∈ Finset.univ.erase k, sI l : ℕ) : ℤ) : ℂ) • ∑ i, cI k i • b i`. Introduce `k`. Rewrite using `[← heqI k, smul_smul, hs, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∀ x ∈ S.La, P ((s : ℂ) • x)`. Introduce `x hx`.

Establish `hx' : x = ∑ k, ((eB.repr ⟨x, hx⟩ k : ℤ) : ℂ) • ((eB k : S.La) : Fin g → ℂ)`. Establish `h` using `congrArg Subtype.val (eB.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hx', Finset.smul_sum]`.

Apply `Finset.sum_induction _ P Padd P0` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[smul_comm, hsk k]`. Conclude with `Pz _ _ (Pz _ _ ⟨cI k, hcI k, rfl⟩)`. Use `⟨s, fun j => (s : ℂ) • bs j, hsq, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j`. Apply `hdual` to reduce the goal to its premises. Introduce `x hx`. Take `⟨c, hc, hce⟩` from `hP x hx`. Take `⟨z, hz⟩` from `hOKint c hc j`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_smul_right, map_natCast, ← hf_smul_left, hce, hz]`. Introduce `i j`. Rewrite using `[hbeta, hf_smul_left, mul_left_comm, hbs j i]`. Break down `eq_or_ne i j with rfl | h` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[h, h.symm]`. Introduce `x hx`. Take `⟨β, hβ⟩ : ∃ β : Fin r → ℂ, ∀ j, beta S.d S.Hm x (b j) = β j` from `⟨_, fun _ => rfl⟩`. Repeatedly rewrite using `[hβ]`.

Establish `hβ' : ∀ i, hf S.Hm x (b i) = (ρ : ℂ)⁻¹ * β i` using `fun i => by`. Rewrite using `[← hβ i, hbeta, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]`. Establish `key : x = ∑ j, β j • bs j`. Take `⟨μ, hμ⟩` from `hmemspan x hx`. Rewrite using `[← sub_eq_zero]`.

Establish `hy : x - ∑ j, β j • bs j = ∑ k, (μ k - ∑ j, β j * ((ρ : ℂ)⁻¹ * A⁻¹ j k)) • b k`. Rewrite using `[hbsdef]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm, ← hμ]`. Rewrite using `[hy]`.

Apply `L0` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← hy, hf_sub_left, hf_sum_left, hβ' i]`. Simplify using `only [hbs2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Use `conv_lhs => rw [key]`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _`.
-/
theorem dual_basis : ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → S.NNBasis q b →
    ∃ (s : ℕ) (c : Fin r → Fin g → ℂ), Nat.Coprime s q ∧ (∀ j, c j ∈ S.La) ∧
      (∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s : ℂ) else 0) ∧
      ∀ x ∈ S.La, (s : ℂ) • x = ∑ j, beta S.d S.Hm x (b j) • c j := by
  intro q _ g S r b hS hb
  obtain ⟨hdp, -, hpos, hdisc, hspan, hw0, -, hdual⟩ := hS
  obtain ⟨hbL, hgen, hind⟩ := hb
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt S.d / 2 := ⟨_, rfl⟩
  have hρ0 : ρ ≠ 0 := by
    have : (0:ℝ) < S.d := by exact_mod_cast hdp.pos
    rw [hρ]; positivity
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  have hbeta : ∀ z w, beta S.d S.Hm z w = (ρ : ℂ) * hf S.Hm z w := fun z w => by rw [hρ]; rfl
  have hw0im : (w0 S.d).im = ρ := by simp [w0, rtd, hρ]
  have hOKim : ∀ c ∈ OK S.d, ∃ v : ℤ, c.im = v * ρ := by
    rintro c ⟨u, v, rfl⟩; exact ⟨v, by simp [hw0im]⟩
  have hqs : ∀ s : ℕ, Nat.Coprime s q → s ≠ 0 := by
    rintro s hs rfl
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hs)

  have hmemspan : ∀ x ∈ S.La, ∃ μ : Fin r → ℂ, x = ∑ i, μ i • b i := by
    intro x hx
    obtain ⟨s, hs, c, -, he⟩ := hgen x hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hqs s hs
    refine ⟨fun i => (s : ℂ)⁻¹ * c i, ?_⟩
    simp_rw [← smul_smul]
    rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have htop : (⊤ : Submodule ℂ (Fin g → ℂ)) ≤ Submodule.span ℂ (Set.range b) := by
    have h1 : Submodule.span ℝ (S.La : Set (Fin g → ℂ)) ≤ (Submodule.span ℂ (Set.range b)).restrictScalars ℝ := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨μ, rfl⟩ := hmemspan x hx
      show _ ∈ Submodule.span ℂ (Set.range b)
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    have : x ∈ Submodule.span ℝ (S.La : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    exact h1 this
  haveI : DiscreteTopology S.La := hdisc
  haveI : IsZLattice ℝ S.La := ⟨hspan⟩
  have hrk : Module.finrank ℤ S.La = 2 * g := by
    rw [ZLattice.rank ℝ S.La]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  have hli2 : LinearIndependent ℤ (fun p : Fin r ⊕ Fin r => (⟨Sum.elim (fun i => b i) (fun i => w0 S.d • b i) p,
      by rcases p with i | i; exacts [hbL i, hw0 _ (hbL i)]⟩ : S.La)) := by
    rw [Fintype.linearIndependent_iff]
    intro n hn
    have hn' := congrArg Subtype.val hn
    simp only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Sum.elim_inl,
      Sum.elim_inr, Submodule.coe_zero] at hn'
    have key : ∑ i, ((n (Sum.inl i) : ℂ) + (n (Sum.inr i) : ℂ) * w0 S.d) • b i = 0 := by
      rw [← hn']
      simp only [add_smul, mul_smul, Finset.sum_add_distrib, Int.cast_smul_eq_zsmul]
    have hc := hind _ (fun i => ⟨n (Sum.inl i), n (Sum.inr i), rfl⟩) key
    have hm : ∀ i, n (Sum.inr i) = 0 := fun i => by
      have := congrArg Complex.im (hc i); simpa [hw0im, hρ0] using this
    have hl : ∀ i, n (Sum.inl i) = 0 := fun i => by
      have := hc i; simp only [hm i, Int.cast_zero, zero_mul, add_zero] at this; exact_mod_cast this
    rintro (i | i); exacts [hl i, hm i]
  have hrg : r ≤ g := by
    have := hli2.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_fin, hrk] at this
    omega
  have hlin : LinearIndependent ℂ b :=
    linearIndependent_of_top_le_span_of_card_le_finrank htop (by simpa using hrg)

  have hconj := hf_conj hpos.isHermitian
  have L0 : ∀ μ : Fin r → ℂ, (∀ i, hf S.Hm (∑ k, μ k • b k) (b i) = 0) → ∑ k, μ k • b k = 0 := by
    intro μ h
    by_contra hne
    apply hf_self_ne hpos hne
    rw [hf_sum_left]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hconj, h k, map_zero, mul_zero]
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin r) (Fin r) ℂ, A = fun i j => hf S.Hm (b i) (b j) := ⟨_, rfl⟩
  have hvm : ∀ w : Fin r → ℂ, ∀ i, Matrix.vecMul w A i = hf S.Hm (∑ k, w k • b k) (b i) := by
    intro w i
    rw [hf_sum_left, hAdef]; rfl
  have hA : IsUnit A := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro u v huv
    have h0 : ∑ k, (u - v) k • b k = 0 := by
      apply L0
      intro i
      have huv' : Matrix.vecMul u A = Matrix.vecMul v A := huv
      rw [← hvm, Matrix.sub_vecMul, huv', sub_self]; rfl
    have := Fintype.linearIndependent_iff.mp hlin (u - v) h0
    funext i; exact sub_eq_zero.mp (this i)
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  obtain ⟨bs, hbsdef⟩ : ∃ bs : Fin r → Fin g → ℂ, bs = fun j => ∑ k, ((ρ : ℂ)⁻¹ * A⁻¹ j k) • b k := ⟨_, rfl⟩
  have hbs : ∀ j i, (ρ : ℂ) * hf S.Hm (bs j) (b i) = if j = i then 1 else 0 := by
    intro j i
    rw [hbsdef]
    simp only [hf_sum_left]
    have := congrFun (congrFun hinv j) i
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρc, one_mul, hAdef]
  have hbs2 : ∀ j i, hf S.Hm (bs j) (b i) = (ρ : ℂ)⁻¹ * (if j = i then 1 else 0) := by
    intro j i; rw [← hbs j i, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]
  have hbs' : ∀ j i, (ρ : ℂ) * hf S.Hm (b i) (bs j) = if j = i then 1 else 0 := by
    intro j i
    rw [hconj, ← Complex.conj_ofReal ρ, ← map_mul, hbs]
    split_ifs <;> simp
  have hOKint : ∀ (c : Fin r → ℂ), (∀ i, c i ∈ OK S.d) → ∀ j, ∃ z : ℤ, (hf S.Hm (∑ i, c i • b i) (bs j)).im = z := by
    intro c hc j
    have e : (ρ : ℂ) * hf S.Hm (∑ i, c i • b i) (bs j) = c j := by
      rw [hf_sum_left, Finset.mul_sum]
      simp_rw [mul_left_comm (ρ : ℂ), hbs']
      simp
    obtain ⟨v, hv⟩ := hOKim _ (hc j)
    refine ⟨v, ?_⟩
    have h2 : hf S.Hm (∑ i, c i • b i) (bs j) = c j / (ρ : ℂ) := by
      rw [← e]; field_simp
    rw [h2, Complex.div_ofReal_im, hv]; field_simp

  have okAdd : ∀ a a', a ∈ OK S.d → a' ∈ OK S.d → a + a' ∈ OK S.d := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩; exact ⟨u + u', v + v', by push_cast; ring⟩
  have okMul : ∀ (n : ℤ) a, a ∈ OK S.d → (n : ℂ) * a ∈ OK S.d := by
    rintro n _ ⟨u, v, rfl⟩; exact ⟨n * u, n * v, by push_cast; ring⟩
  have ok0 : (0 : ℂ) ∈ OK S.d := ⟨0, 0, by simp⟩
  let P : (Fin g → ℂ) → Prop := fun y => ∃ c : Fin r → ℂ, (∀ i, c i ∈ OK S.d) ∧ y = ∑ i, c i • b i
  have Padd : ∀ y y', P y → P y' → P (y + y') := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun i => okAdd _ _ (hc i) (hc' i), by simp [add_smul, Finset.sum_add_distrib]⟩
  have P0 : P 0 := ⟨0, fun _ => ok0, by simp⟩
  have Pz : ∀ (n : ℤ) y, P y → P ((n : ℂ) • y) := by
    rintro n _ ⟨c, hc, rfl⟩
    exact ⟨fun i => (n : ℂ) * c i, fun i => okMul n _ (hc i), by rw [Finset.smul_sum]; simp [smul_smul]⟩

  haveI : Module.Finite ℤ S.La := ZLattice.module_finite ℝ S.La
  haveI : Module.Free ℤ S.La := ZLattice.module_free ℝ S.La
  obtain ⟨ι, _, ⟨eB⟩⟩ : ∃ (ι : Type) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ S.La) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ S.La⟩⟩
  classical
  choose sI hsI cI hcI heqI using fun k : ι => hgen _ (eB k).2
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ∏ k, sI k := ⟨_, rfl⟩
  have hsq : Nat.Coprime s q := hs ▸ Nat.Coprime.prod_left fun k _ => hsI k
  have hsk : ∀ k, (s : ℂ) • ((eB k : S.La) : Fin g → ℂ) =
      (((∏ l ∈ Finset.univ.erase k, sI l : ℕ) : ℤ) : ℂ) • ∑ i, cI k i • b i := by
    intro k
    rw [← heqI k, smul_smul, hs, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    congr 1; push_cast; ring
  have hP : ∀ x ∈ S.La, P ((s : ℂ) • x) := by
    intro x hx
    have hx' : x = ∑ k, ((eB.repr ⟨x, hx⟩ k : ℤ) : ℂ) • ((eB k : S.La) : Fin g → ℂ) := by
      have h := congrArg Subtype.val (eB.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      calc x = ∑ k, eB.repr ⟨x, hx⟩ k • ((eB k : S.La) : Fin g → ℂ) := h.symm
        _ = _ := Finset.sum_congr rfl fun k _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [hx', Finset.smul_sum]
    apply Finset.sum_induction _ P Padd P0
    intro k _
    rw [smul_comm, hsk k]
    exact Pz _ _ (Pz _ _ ⟨cI k, hcI k, rfl⟩)
  refine ⟨s, fun j => (s : ℂ) • bs j, hsq, ?_, ?_, ?_⟩
  · intro j
    apply hdual
    intro x hx
    obtain ⟨c, hc, hce⟩ := hP x hx
    obtain ⟨z, hz⟩ := hOKint c hc j
    refine ⟨z, ?_⟩
    rw [hf_smul_right, map_natCast, ← hf_smul_left, hce, hz]
  · intro i j
    rw [hbeta, hf_smul_left, mul_left_comm, hbs j i]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, h.symm]
  · intro x hx
    obtain ⟨β, hβ⟩ : ∃ β : Fin r → ℂ, ∀ j, beta S.d S.Hm x (b j) = β j := ⟨_, fun _ => rfl⟩
    simp_rw [hβ]
    have hβ' : ∀ i, hf S.Hm x (b i) = (ρ : ℂ)⁻¹ * β i := fun i => by
      rw [← hβ i, hbeta, ← mul_assoc, inv_mul_cancel₀ hρc, one_mul]
    have key : x = ∑ j, β j • bs j := by
      obtain ⟨μ, hμ⟩ := hmemspan x hx
      rw [← sub_eq_zero]
      have hy : x - ∑ j, β j • bs j = ∑ k, (μ k - ∑ j, β j * ((ρ : ℂ)⁻¹ * A⁻¹ j k)) • b k := by
        rw [hbsdef]
        simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm, ← hμ]
      rw [hy]
      apply L0
      intro i
      rw [← hy, hf_sub_left, hf_sum_left, hβ' i]
      simp only [hbs2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    conv_lhs => rw [key]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.MomDual
