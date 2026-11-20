import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW

variable {p : ℕ} [Fact p.Prime] {r n : ℕ}

def swappedDualWeyl (p : ℕ) [Fact p.Prime] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) :=
  Submodule.map (swp ℚ_[p] r n).toLinearMap (dualWeyl ℚ_[p] r n ν)

/- English proof (translation)
Assemble the required witnesses or components as `⟨f, hf, rfl⟩`.
-/
theorem swap_mem_swappedDualWeyl {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℚ_[p]} (hf : f ∈ dualWeyl ℚ_[p] r n ν) :
    swp ℚ_[p] r n f ∈ swappedDualWeyl p r n ν := ⟨f, hf, rfl⟩

/- English proof (translation)
Introduce and unpack `x ⟨f, hf, rfl⟩`. Conclude with `hP p r n ν f hf.1`.
-/
theorem cor_W_le_pol (hP : SwpPol) (ν : Fin n → ℕ) : swappedDualWeyl p r n ν ≤ Pol p r (vecL ν) := by
  rintro x ⟨f, hf, rfl⟩
  exact hP p r n ν f hf.1

/- English proof (translation)
Introduce and unpack `a b x ⟨f, hf, rfl⟩`. Conclude with `⟨rowDiv ℚ_[p] a b 1 f, rowDivStable ℚ_[p] r n ν a b 1 f hf, h1 p r n ν a b f⟩`.
-/
theorem cor_stable (h1 : RowGlOne) (ν : Fin n → ℕ) : (GR p r ν).Stable (swappedDualWeyl p r n ν) := by
  rintro a b x ⟨f, hf, rfl⟩
  exact ⟨rowDiv ℚ_[p] a b 1 f, rowDivStable ℚ_[p] r n ν a b 1 f hf, h1 p r n ν a b f⟩

/- English proof (translation)
Introduce and unpack `μ μ' x y hx0 hy0 ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩ hμ hμ' c`. Establish `hf0 : f ≠ 0` using `fun h => hx0 (by rw [h, map_zero])`. Establish `hg0 : g ≠ 0` using `fun h => hy0 (by rw [h, map_zero])`. Take `⟨m, hm⟩` from `(MvPolynomial.support_nonempty).mpr hf0`. Take `⟨m', hm'⟩` from `(MvPolynomial.support_nonempty).mpr hg0`.

Establish `e1` using `(hw p r n ν μ f).mp hμ m hm c`. Establish `e2` using `(hw p r n ν μ' g).mp hμ' m' hm' c`. Establish `i1` using `hS f hf g hg m hm m' hm' c`. Establish `i2` using `hS g hg f hf m' hm' m hm c`. Rewrite using `[← e1, ← e2, abs_le]`.

Apply the tactic sequence `constructor <;> omega`.
-/
theorem cor_bound (hw : SwpWt) (ν : Fin n → ℕ) (l : ℕ) (hS : Spread ℚ_[p] r n ν l) :
    ∀ (μ μ' : Fin r → ℤ) (x y : MvPolynomial (Fin n × Fin r) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ swappedDualWeyl p r n ν → y ∈ swappedDualWeyl p r n ν → (GR p r ν).IsWt μ x → (GR p r ν).IsWt μ' y →
      ∀ c, |μ' c - μ c| ≤ (l : ℤ) := by
  rintro μ μ' x y hx0 hy0 ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩ hμ hμ' c
  have hf0 : f ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hg0 : g ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  obtain ⟨m, hm⟩ := (MvPolynomial.support_nonempty).mpr hf0
  obtain ⟨m', hm'⟩ := (MvPolynomial.support_nonempty).mpr hg0
  have e1 := (hw p r n ν μ f).mp hμ m hm c
  have e2 := (hw p r n ν μ' g).mp hμ' m' hm' c
  have i1 := hS f hf g hg m hm m' hm' c
  have i2 := hS g hg f hf m' hm' m hm c
  rw [← e1, ← e2, abs_le]
  constructor <;> omega

/- English proof (translation)
Establish `D` using `polLatData_of Formalism.InvariantFactorPaths.PW.Top.latBasisPol (p := p) (r := r) (vecL ν) (vecL ν) n (OrderIso.refl (Fin r)).toOrderEmbedding`. Conclude with `{ stable := cor_stable h1 ν fd := by`. Use `D.fd` as an intermediate fact. Conclude with `Submodule.finiteDimensional_of_le (cor_W_le_pol hP ν)`. Use `finW := by`.

Take `⟨S, hS'⟩` from `D.finW`. Conclude with `⟨S, fun x hx => hS' x (cor_W_le_pol hP ν hx)⟩`. Use `bound := cor_bound hw ν l hS`. Use `closed := D.closed`. Use `div := D.div`.

Use `graded := D.graded`. Use `basis := fun U hU => D.basis U (hU.trans (cor_W_le_pol hP ν)) }`.
-/
theorem cor_latData (h1 : RowGlOne) (hw : SwpWt) (hP : SwpPol) (ν : Fin n → ℕ) (l : ℕ)
    (hS : Spread ℚ_[p] r n ν l) :
    LatData p (GR p r ν) (swappedDualWeyl p r n ν) (IntPol p (Fin n × Fin r)).toAddSubgroup l := by
  have D := polLatData_of Formalism.InvariantFactorPaths.PW.Top.latBasisPol (p := p) (r := r) (vecL ν) (vecL ν) n
    (OrderIso.refl (Fin r)).toOrderEmbedding
  exact
    { stable := cor_stable h1 ν
      fd := by
        have := D.fd
        exact Submodule.finiteDimensional_of_le (cor_W_le_pol hP ν)
      finW := by
        obtain ⟨S, hS'⟩ := D.finW
        exact ⟨S, fun x hx => hS' x (cor_W_le_pol hP ν hx)⟩
      bound := cor_bound hw ν l hS
      closed := D.closed
      div := D.div
      graded := D.graded
      basis := fun U hU => D.basis U (hU.trans (cor_W_le_pol hP ν)) }

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW r n i) (fun _ => zero_smul _ _), Finset.sum_apply, Fintype.sum_prod_type, rowDeg]`. Simplify using `only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem cor_weight_rowW (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW r n i) (fun _ => zero_smul _ _),
    Finset.sum_apply, Fintype.sum_prod_type, rowDeg]
  simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

def swappedHighestWeight (p : ℕ) [Fact p.Prime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : MvPolynomial (Fin n × Fin r) ℚ_[p] :=
  swp ℚ_[p] r n (hw ℚ_[p] hn ν)

/- English proof (translation)
The claim follows from `swap_mem_swappedDualWeyl (hwMem ℚ_[p] r n hn ν hν)`.
-/
theorem swapped_highest_weight_mem (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) : swappedHighestWeight p hn ν ∈ swappedDualWeyl p r n ν :=
  swap_mem_swappedDualWeyl (hwMem ℚ_[p] r n hn ν hν)

/- English proof (translation)
Introduce `h`. Conclude with `hwNe ℚ_[p] r n hn ν ((swp ℚ_[p] r n).injective (by rw [map_zero]; exact h))`.
-/
theorem swapped_highest_weight_ne_zero (hn : n ≤ r) (ν : Fin n → ℕ) : swappedHighestWeight p hn ν ≠ 0 := by
  intro h
  exact hwNe ℚ_[p] r n hn ν ((swp ℚ_[p] r n).injective (by rw [map_zero]; exact h))

/- English proof (translation)
Use `⟨(hw' p r n ν _ _).mpr fun m hm a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `hwRowWeight ℚ_[p] r n hn ν hν (mem_support_iff.mp hm)` as an intermediate fact. Rewrite using `[← cor_weight_rowW, this]`. Rewrite using `[swappedHighestWeight, ← h1 p r n ν a b, hwRaise ℚ_[p] r n hn ν a b 1 hab le_rfl, map_zero]`.
-/
theorem swapped_highest_weight_isHW (h1 : RowGlOne) (hw' : SwpWt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (GR p r ν).IsHW (fun a => (rowNu ν a : ℤ)) (swappedHighestWeight p hn ν) := by
  refine ⟨(hw' p r n ν _ _).mpr fun m hm a => ?_, fun a b hab => ?_⟩
  · have := hwRowWeight ℚ_[p] r n hn ν hν (mem_support_iff.mp hm)
    rw [← cor_weight_rowW, this]
  · rw [swappedHighestWeight, ← h1 p r n ν a b, hwRaise ℚ_[p] r n hn ν a b 1 hab le_rfl, map_zero]

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hv`. Take `⟨c, hc⟩` from `hwLine ℚ_[p] r n hn ν hν f hf (by`. Introduce `a b hab k hk1`. Apply `(swp ℚ_[p] r n).injective` to reduce the goal to its premises. Rewrite using `[hk p r n ν a b hab.ne k f, map_zero]`.

Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Establish `h0 : (GR p r ν).E a b (swp ℚ_[p] r n f) = 0` using `hh.2 a b hab`. Rewrite using `[pow_succ, Module.End.mul_apply, h0, map_zero, smul_zero])`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[swappedHighestWeight, ← map_smul, ← hc]`.

Both sides reduce to the same expression.
-/
theorem cor_line (hk : RowGlDiv) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (μ : Fin r → ℤ)
    (v : MvPolynomial (Fin n × Fin r) ℚ_[p]) (hv : v ∈ swappedDualWeyl p r n ν) (hh : (GR p r ν).IsHW μ v) :
    ∃ c : ℚ_[p], v = c • swappedHighestWeight p hn ν := by
  obtain ⟨f, hf, rfl⟩ := hv
  obtain ⟨c, hc⟩ := hwLine ℚ_[p] r n hn ν hν f hf (by
    intro a b hab k hk1
    apply (swp ℚ_[p] r n).injective
    rw [hk p r n ν a b hab.ne k f, map_zero]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : (GR p r ν).E a b (swp ℚ_[p] r n f) = 0 := hh.2 a b hab
    rw [pow_succ, Module.End.mul_apply, h0, map_zero, smul_zero])
  refine ⟨c, ?_⟩
  rw [swappedHighestWeight, ← map_smul, ← hc]
  rfl

/- English proof (translation)
Take `⟨S, hS⟩` from `GAe_pol_finW (p := p) (r := r) (vecL ν) (vecL ν) n (OrderIso.refl (Fin r)).toOrderEmbedding`. Establish `h` using `Formalism.CountingSumsFrames.GlX.span_hw (GR p r ν) (cor_stable h1 ν) (S := S) (fun x hx => hS x (cor_W_le_pol hP ν hx)) (fun _ : Unit => swappedHighestWeight p hn ν) (fun _ a => (rowNu ν a : ℤ)) (fun _ => swapped_highest_weight_isHW h1 hw' hn ν hν) (fun _ => swapped_highest_weig …`. Introduce `μ v hv hh`. Take `⟨c, rfl⟩` from `cor_line hk hn ν hν μ v hv hh`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩))`.

Use `h.trans (iSup_le fun _ => ?_)` and prove the remaining obligations. Use `(GR p r ν).gS_le ?_ ((GR p r ν).gS_stable _)` and prove the remaining obligations. Rewrite using `[Set.singleton_subset_iff]`. Conclude with `(GR p r ν).subset_gS _ ⟨swapped_highest_weight_isHW h1 hw' hn ν hν, swapped_highest_weight_mem hn ν hν⟩`.
-/
theorem cor_W_le_iso (h1 : RowGlOne) (hk : RowGlDiv) (hw' : SwpWt) (hP : SwpPol) (hn : n ≤ r) (ν : Fin n → ℕ)
    (hν : Antitone ν) :
    swappedDualWeyl p r n ν ≤ IsoW (GR p r ν) (swappedDualWeyl p r n ν) (fun a => (rowNu ν a : ℤ)) := by
  obtain ⟨S, hS⟩ := GAe_pol_finW (p := p) (r := r) (vecL ν) (vecL ν) n (OrderIso.refl (Fin r)).toOrderEmbedding
  have h := Formalism.CountingSumsFrames.GlX.span_hw (GR p r ν) (cor_stable h1 ν) (S := S)
    (fun x hx => hS x (cor_W_le_pol hP ν hx)) (fun _ : Unit => swappedHighestWeight p hn ν)
    (fun _ a => (rowNu ν a : ℤ)) (fun _ => swapped_highest_weight_isHW h1 hw' hn ν hν) (fun _ => swapped_highest_weight_mem hn ν hν)
    (fun _ => swapped_highest_weight_ne_zero hn ν) (by
      intro μ v hv hh
      obtain ⟨c, rfl⟩ := cor_line hk hn ν hν μ v hv hh
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩))
  refine h.trans (iSup_le fun _ => ?_)
  refine (GR p r ν).gS_le ?_ ((GR p r ν).gS_stable _)
  rw [Set.singleton_subset_iff]
  exact (GR p r ν).subset_gS _ ⟨swapped_highest_weight_isHW h1 hw' hn ν hν, swapped_highest_weight_mem hn ν hν⟩

def cor_emb (p : ℕ) [Fact p.Prime] (r n : ℕ) :
    MvPolynomial (Fin r × Fin n) ℤ_[p] →ₗ[ℤ_[p]] MvPolynomial (Fin n × Fin r) ℚ_[p] :=
  ((swp ℚ_[p] r n).toLinearMap.restrictScalars ℤ_[p]) ∘ₗ (mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cor_emb_apply (y : MvPolynomial (Fin r × Fin n) ℤ_[p]) :
    cor_emb p r n y = swp ℚ_[p] r n (map (algebraMap ℤ_[p] ℚ_[p]) y) := rfl

/- English proof (translation)
Introduce `x y h`. Rewrite `h` using `[cor_emb_apply, cor_emb_apply]`. Conclude with `MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) ((swp ℚ_[p] r n).injective h)`.
-/
theorem cor_emb_inj : Function.Injective (cor_emb p r n) := by
  intro x y h
  rw [cor_emb_apply, cor_emb_apply] at h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) ((swp ℚ_[p] r n).injective h)

/- English proof (translation)
Rewrite using `[cor_emb_apply, lclosedeq_hw_map, swappedHighestWeight]`.
-/
theorem cor_emb_hw (hn : n ≤ r) (ν : Fin n → ℕ) : cor_emb p r n (hw ℤ_[p] hn ν) = swappedHighestWeight p hn ν := by
  rw [cor_emb_apply, lclosedeq_hw_map, swappedHighestWeight]

def cor_L (p : ℕ) [Fact p.Prime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin n × Fin r) ℚ_[p]) :=
  Submodule.map (cor_emb p r n) (weyl ℤ_[p] r n hn ν)

/- English proof (translation)
Introduce and unpack `a b hab k x ⟨y, hy, rfl⟩`. Use `⟨rowDiv ℤ_[p] a b k y, weylRowDivStable ℤ_[p] r n hn ν a b k y hy, ?_⟩` and prove the remaining obligations. Rewrite using `[cor_emb_apply, cor_emb_apply, ← lclosedeq_rowDiv_map, hk p r n ν a b hab k]`.
-/
theorem cor_L_div (hk : RowGlDiv) (hn : n ≤ r) (ν : Fin n → ℕ) :
    DivStable (GR p r ν).E (cor_L p hn ν).toAddSubgroup := by
  rintro a b hab k x ⟨y, hy, rfl⟩
  refine ⟨rowDiv ℤ_[p] a b k y, weylRowDivStable ℤ_[p] r n hn ν a b k y hy, ?_⟩
  rw [cor_emb_apply, cor_emb_apply, ← lclosedeq_rowDiv_map, hk p r n ν a b hab k]

/- English proof (translation)
Simplify using `only [hw, map_prod, map_pow, eval_idPoint_lpMinor, one_pow, Finset.prod_const_one]`.
-/
theorem cor_eval_hw (R : Type) [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idPoint R r n) (hw R hn ν) = 1 := by
  simp only [hw, map_prod, map_pow, eval_idPoint_lpMinor, one_pow, Finset.prod_const_one]

/- English proof (translation)
Rewrite using `[eval_map, eval, coe_eval₂Hom, eval₂_comp_left]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Simplify using `only [idPoint, Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem cor_eval_map (f0 : MvPolynomial (Fin r × Fin n) ℤ_[p]) :
    eval (idPoint ℚ_[p] r n) (map (algebraMap ℤ_[p] ℚ_[p]) f0) =
      algebraMap ℤ_[p] ℚ_[p] (eval (idPoint ℤ_[p] r n) f0) := by
  rw [eval_map, eval, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  funext v
  simp only [idPoint, Function.comp_apply]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨c, rfl⟩` from `cor_line hk hn ν hν μ h hW hh`. Rewrite `hM` using `[swappedHighestWeight, ← map_smul]`. Take `⟨f0, hf0⟩` from `(hI p r n _).mp hM`. Establish `hc : algebraMap ℤ_[p] ℚ_[p] (eval (idPoint ℤ_[p] r n) f0) = c`. Rewrite using `[← cor_eval_map, hf0, smul_eq_C_mul, map_mul, eval_C, cor_eval_hw, mul_one]`.

Use `⟨eval (idPoint ℤ_[p] r n) f0 • hw ℤ_[p] hn ν, Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, cor_emb_hw, ← hc, algebraMap_smul]`.
-/
theorem cor_gen (hk : RowGlDiv) (hI : SwpInt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (μ : Fin r → ℤ)
    (h : MvPolynomial (Fin n × Fin r) ℚ_[p]) (hh : (GR p r ν).IsHW μ h) (hW : h ∈ swappedDualWeyl p r n ν)
    (hM : h ∈ IntPol p (Fin n × Fin r)) : h ∈ cor_L p hn ν := by
  obtain ⟨c, rfl⟩ := cor_line hk hn ν hν μ h hW hh
  rw [swappedHighestWeight, ← map_smul] at hM
  obtain ⟨f0, hf0⟩ := (hI p r n _).mp hM
  have hc : algebraMap ℤ_[p] ℚ_[p] (eval (idPoint ℤ_[p] r n) f0) = c := by
    rw [← cor_eval_map, hf0, smul_eq_C_mul, map_mul, eval_C, cor_eval_hw, mul_one]
  refine ⟨eval (idPoint ℤ_[p] r n) f0 • hw ℤ_[p] hn ν,
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩), ?_⟩
  rw [map_smul, cor_emb_hw, ← hc, algebraMap_smul]

/- English proof (translation)
Use `sInf_le ⟨?_, zpClosed_toAddSubgroup _, cor_L_div hk hn ν⟩` and prove the remaining obligations. Introduce and unpack `h ⟨a1, a2, a3⟩`. Conclude with `cor_gen hk hI hn ν hν la h a1 a2 a3`.
-/
theorem cor_delta_le (hk : RowGlDiv) (hI : SwpInt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (la : Fin r → ℤ) :
    DeltaLat p (GR p r ν) {h | (GR p r ν).IsHW la h ∧ h ∈ swappedDualWeyl p r n ν ∧
      h ∈ (IntPol p (Fin n × Fin r)).toAddSubgroup} ≤ (cor_L p hn ν).toAddSubgroup := by
  refine sInf_le ⟨?_, zpClosed_toAddSubgroup _, cor_L_div hk hn ν⟩
  rintro h ⟨a1, a2, a3⟩
  exact cor_gen hk hI hn ν hν la h a1 a2 a3

/- English proof (translation)
Introduce `p _ r n hn ν hν l hS x hx`. Establish `hXW : cor_emb p r n x ∈ swappedDualWeyl p r n ν` using `swap_mem_swappedDualWeyl (dualWeylMap ℤ_[p] ℚ_[p] (algebraMap ℤ_[p] ℚ_[p]) r n ν x hx)`. Establish `hXM : cor_emb p r n x ∈ (IntPol p (Fin n × Fin r)).toAddSubgroup` using `(hI p r n _).mpr ⟨x, rfl⟩`. Establish `h` using `Formalism.InvariantFactorPaths.PW.Top.weylInt p _ r (GR p r ν) (swappedDualWeyl p r n ν) (IntPol p (Fin n × Fin r)).toAddSubgroup l (cor_latData h1 hw hP ν l hS) (fun a => (rowNu ν a : ℤ)) (cor_emb p r n x) (cor_W_le_iso h1 hk hw hP hn ν hν hXW) hXM`. Take `⟨y, hy, hyx⟩` from `cor_delta_le hk hI hn ν hν _ h`.

Establish `e : ((p : ℚ_[p]) ^ (r.choose 2 * Nat.log p (l + r - 1))) • cor_emb p r n x = cor_emb p r n (((p : ℤ_[p]) ^ sExp p r l) • x)`. Rewrite using `[map_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ sExp p r l), map_pow, map_natCast, sExp, Nat.choose_two_right]`. Rewrite `hyx` using `[e]`. Rewrite using `[← cor_emb_inj hyx]`. Conclude with `hy`.
-/
theorem coreQp_of (h1 : RowGlOne) (hk : RowGlDiv) (hw : SwpWt) (hP : SwpPol) (hI : SwpInt) : CoreQp := by
  intro p _ r n hn ν hν l hS x hx
  have hXW : cor_emb p r n x ∈ swappedDualWeyl p r n ν :=
    swap_mem_swappedDualWeyl (dualWeylMap ℤ_[p] ℚ_[p] (algebraMap ℤ_[p] ℚ_[p]) r n ν x hx)
  have hXM : cor_emb p r n x ∈ (IntPol p (Fin n × Fin r)).toAddSubgroup :=
    (hI p r n _).mpr ⟨x, rfl⟩
  have h := Formalism.InvariantFactorPaths.PW.Top.weylInt p _ r (GR p r ν) (swappedDualWeyl p r n ν) (IntPol p (Fin n × Fin r)).toAddSubgroup l
    (cor_latData h1 hw hP ν l hS) (fun a => (rowNu ν a : ℤ)) (cor_emb p r n x)
    (cor_W_le_iso h1 hk hw hP hn ν hν hXW) hXM
  obtain ⟨y, hy, hyx⟩ := cor_delta_le hk hI hn ν hν _ h
  have e : ((p : ℚ_[p]) ^ (r.choose 2 * Nat.log p (l + r - 1))) • cor_emb p r n x =
      cor_emb p r n (((p : ℤ_[p]) ^ sExp p r l) • x) := by
    rw [map_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ sExp p r l), map_pow, map_natCast, sExp,
      Nat.choose_two_right]
  rw [e] at hyx
  rw [← cor_emb_inj hyx]
  exact hy

end Formalism.InvariantFactorPaths.INST
