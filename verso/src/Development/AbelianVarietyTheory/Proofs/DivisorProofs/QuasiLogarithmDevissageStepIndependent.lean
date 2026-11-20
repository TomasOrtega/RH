import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DevStep

/- English proof (translation)
Introduce `α` and use `by obtain ⟨x, hx, hfx⟩ := hf α obtain ⟨y, hy, hgy⟩ := hg α exact ⟨x - y, N.sub_mem hx hy, by rw [map_sub, map_sub, hfx, hgy]⟩`.
-/
theorem in_sub {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f - g) := fun α => by
  obtain ⟨x, hx, hfx⟩ := hf α
  obtain ⟨y, hy, hgy⟩ := hg α
  exact ⟨x - y, N.sub_mem hx hy, by rw [map_sub, map_sub, hfx, hgy]⟩

/- English proof (translation)
Use `choose g hgN hg using hf`. Set `G : MvPowerSeries σ B` to `fun α => g α`. Establish `hfG : f = map (algebraMap B Q) G` using `by ext α; rw [coeff_map, hg]; rfl`. Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Introduce `α`.

Use `⟨coeff α (subst a G), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs G α)]`. Conclude with `Ideal.sum_mem _ fun d _ => by rw [smul_eq_mul]; exact N.mul_mem_right _ (hgN d)`. Rewrite using `[hfG, ← map_subst hs, coeff_map]`.
-/
theorem in_subst {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Finite σ] {N : Ideal B}
    {a : σ → MvPowerSeries τ B} (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (subst (fun i => map (algebraMap B Q) (a i)) f) := by
  choose g hgN hg using hf
  let G : MvPowerSeries σ B := fun α => g α
  have hfG : f = map (algebraMap B Q) G := by ext α; rw [coeff_map, hg]; rfl
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  intro α
  refine ⟨coeff α (subst a G), ?_, ?_⟩
  · rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs G α)]
    exact Ideal.sum_mem _ fun d _ => by rw [smul_eq_mul]; exact N.mul_mem_right _ (hgN d)
  · rw [hfG, ← map_subst hs, coeff_map]

/- English proof (translation)
Unfold `cob1 inL inR`. Establish `hl : (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun i => map (algebraMap B Q) (X (Sum.inl i))` using `by funext i; rw [map_X]`. Establish `hr : (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun i => map (algebraMap B Q) (X (Sum.inr i))` using `by funext i; rw [map_X]`. Rewrite using `[hl, hr]`. Conclude with `in_sub (in_sub (in_subst hμ hf) (in_subst (fun _ => constantCoeff_X _) hf)) (in_subst (fun _ => constantCoeff_X _) hf)`.
-/
theorem coeffsInIdeal_formalGroupLawCoboundaryOne {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} {N : Ideal B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In N f) : In N (cob1 (up Q μ) f) := by
  unfold cob1 inL inR
  have hl : (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
      fun i => map (algebraMap B Q) (X (Sum.inl i)) := by funext i; rw [map_X]
  have hr : (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
      fun i => map (algebraMap B Q) (X (Sum.inr i)) := by funext i; rw [map_X]
  rw [hl, hr]
  exact in_sub (in_sub (in_subst hμ hf) (in_subst (fun _ => constantCoeff_X _) hf))
    (in_subst (fun _ => constantCoeff_X _) hf)

/- English proof (translation)
Establish `h1 : HasSubst (up Q μ)` using `hasSubst_of_constantCoeff_zero fun i => by`. Simplify using `[up, hμ i]`. Establish `h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Unfold `cob1 inL inR`.

Rewrite using `[map_sub, map_sub, map_subst h1, map_subst h2, map_subst h3]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Use extensionality with `α`. Simplify using `[up, coeff_map, hΘ]`.

Use function extensionality and compare the values at `i`. Rewrite using `[map_X]`. Use function extensionality and compare the values at `i`. Rewrite using `[map_X]`.
-/
theorem map_formalGroupLawCoboundaryOne_eq {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
    [Algebra O C] {d : ℕ} (θ : B →+* O) (Θ : Q →+* C)
    (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ) f) = cob1 (up C fun i => map θ (μ i)) (map Θ f) := by
  have h1 : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, hμ i]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst h1, map_subst h2, map_subst h3]
  congr 3
  · funext i; ext α; simp [up, coeff_map, hΘ]
  · funext i; rw [map_X]
  · funext i; rw [map_X]

def coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) : Submodule B Q :=
  Submodule.map (Algebra.linearMap B Q) N

/- English proof (translation)
Simplify using `only [coeffIdeal, Submodule.mem_map, Algebra.linearMap_apply]`. Conclude with `⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩`.
-/
theorem mem_coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B} {q : Q} :
    q ∈ coeffIdeal N ↔ ∃ b ∈ N, q = algebraMap B Q b := by
  simp only [coeffIdeal, Submodule.mem_map, Algebra.linearMap_apply]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩

/- English proof (translation)
Take `⟨y, -, rfl⟩` from `mem_coeffIdeal.1 hq`. Conclude with `mem_coeffIdeal.2 ⟨r * y, N.mul_mem_right _ hr, (map_mul _ _ _).symm⟩`.
-/
theorem mul_mem_coeffIdeal {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {r : B} (hr : r ∈ N) {q : Q} (hq : q ∈ coeffIdeal (⊤ : Ideal B)) :
    algebraMap B Q r * q ∈ coeffIdeal N := by
  obtain ⟨y, -, rfl⟩ := mem_coeffIdeal.1 hq
  exact mem_coeffIdeal.2 ⟨r * y, N.mul_mem_right _ hr, (map_mul _ _ _).symm⟩

/- English proof (translation)
Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ r hq`.
-/
theorem mul_mem_coeffIdeal' {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    (r : B) {q : Q} (hq : q ∈ coeffIdeal N) : algebraMap B Q r * q ∈ coeffIdeal N := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r hq

end GlobalTheory.DevStep

open GlobalTheory.DevStep in

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ hF d μ hμ C _ _ hC Θ hΘ ι _ e he hB N' N hstep b s hb hs hQL`. Take `⟨n, a, ⟨c, hc⟩, hN, hn⟩` from `hstep`. Establish `hμ0` using `hμ.const`. Establish `hup0 : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by simp [up, hμ0 i]`. Establish `hdec : ∀ x ∈ N, ∃ m ∈ N', ∃ t : B, x = m + t * n`.

Introduce `x hx`. Rewrite `hx` using `[hN, Submodule.mem_sup]`. Take `⟨m, hm, z, hz, rfl⟩` from `hx`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Conclude with `⟨m, hm, t, rfl⟩`.

Use `choose n' hn' β hβ using fun i => hdec (b i) (hb i)`. Establish `hcomb : ∀ (w : ι → B) α, coeff α (comb w e) = ∑ i, algebraMap B Q (w i) * coeff α (e i)`. Introduce `w α`. Simplify using `only [comb, map_sum, coeff_smul, smul_eq_mul]`. Establish `he0 : ∀ i, coeff 0 (e i) = 0` using `fun i => by`.

Rewrite using `[coeff_zero_eq_constantCoeff_apply]`. Conclude with `(he i).1`. Establish `hs0 : coeff 0 s = 0`. Establish `h` using `hQL.1`. Rewrite `h` using `[← coeff_zero_eq_constantCoeff_apply, map_sub, hcomb]`.

Simplify `h` using `[he0]`. Establish `hsdec : ∀ α, ∃ m ∈ N', ∃ t : B, coeff α s = algebraMap B Q (m + t * n) ∧ (α = 0 → t = 0)`. Introduce `α`. Distinguish the cases in `h0 : α = 0`. Conclude with `⟨0, N'.zero_mem, 0, by rw [h0, hs0]; simp, fun _ => rfl⟩`.

Take `⟨x, hx, hxs⟩` from `hs α`. Take `⟨m, hm, t, rfl⟩` from `hdec x hx`. Conclude with `⟨m, hm, t, hxs, fun h => absurd h h0⟩`. Use `choose m hm t hts ht0 using hsdec`. Set `S' : MvPowerSeries (Fin d) Q` to `map (algebraMap B Q) (fun α => m α)`.

Set `S₁ : MvPowerSeries (Fin d) Q` to `map (algebraMap B Q) (fun α => t α)`. Establish `cS' : ∀ α, coeff α S' = algebraMap B Q (m α)` using `fun α => by simp only [S', coeff_map]; rfl`. Establish `cS₁ : ∀ α, coeff α S₁ = algebraMap B Q (t α)` using `fun α => by simp only [S₁, coeff_map]; rfl`. Establish `hS' : In N' S'` using `fun α => ⟨m α, hm α, cS' α⟩`. Establish `hS₁ : In (⊤ : Ideal B) S₁` using `fun α => ⟨t α, trivial, cS₁ α⟩`.

Take `⟨E, hE⟩ : ∃ E, E = comb β e - S₁` from `⟨_, rfl⟩`. Establish `cE : ∀ α, coeff α E = ∑ i, algebraMap B Q (β i) * coeff α (e i) - algebraMap B Q (t α)`. Introduce `α`. Rewrite using `[hE, map_sub, hcomb, cS₁]`. Establish `hkey : comb b e - s = (comb n' e - S') + algebraMap B Q n • E`.

Use extensionality with `α`. Rewrite using `[map_sub, map_add, map_sub, coeff_smul, cE, hcomb, hcomb, hts, cS']`. Simplify using `only [hβ, map_add, map_mul, add_mul, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]`. Put the polynomial expressions in normal form. Set `L : MvPowerSeries (Fin d) Q →ₗ[Q] MvPowerSeries (Fin d ⊕ Fin d) Q` to `{ toFun := cob1 (up Q μ), map_add' := formalCoboundary_add hup0, map_smul' := formalCoboundary_smul hup0 }`.

Establish `hL : ∀ f, L f = cob1 (up Q μ) f` using `fun _ => rfl`. Establish `hcobcomb : ∀ (w : ι → B) α, coeff α (cob1 (up Q μ) (comb w e)) = ∑ i, algebraMap B Q (w i) * coeff α (cob1 (up Q μ) (e i))`. Introduce `w α`. Rewrite using `[← hL]`. Unfold `comb`.

Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, coeff_smul]`. Both sides reduce to the same expression. Establish `hdiv : ∀ q : Q, q ∈ coeffIdeal (⊤ : Ideal B) → algebraMap B Q n * q ∈ coeffIdeal N' → ∃ y, q = algebraMap B Q y ∧ a ∣ θ y`.

Introduce `q hq hnq`. Take `⟨y, -, rfl⟩` from `mem_coeffIdeal.1 hq`. Take `⟨x, hx, hxy⟩` from `mem_coeffIdeal.1 hnq`. Use `⟨y, rfl, (hn y).1 ?_⟩` and prove the remaining obligations. Rewrite `hxy` using `[← map_mul]`.

Rewrite using `[mul_comm, hF.inj hxy]`. Conclude with `hx`. Establish `hl : ∀ (f : MvPowerSeries (Fin d) Q) i, lin f i = coeff (Finsupp.single i 1) f` using `fun _ _ => rfl`. Establish `hlinE : ∀ i, ∃ y, lin E i = algebraMap B Q y ∧ a ∣ θ y`. Introduce `i`.

Establish `hej : ∀ j, coeff (Finsupp.single i 1) (e j) ∈ coeffIdeal (⊤ : Ideal B)` using `fun j => by`. Take `⟨y, hy, h⟩` from `(he j).2.1 i`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, by rw [← hl]; exact h⟩`. Apply `hdiv` to reduce the goal to its premises. Rewrite using `[hl, cE]`.

Conclude with `Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j)) (mem_coeffIdeal.2 ⟨_, trivial, rfl⟩)`. Establish `h1` using `congrArg (coeff (Finsupp.single i 1)) hkey`. Rewrite `h1` using `[map_add, coeff_smul]`. Establish `h2 : algebraMap B Q n * coeff (Finsupp.single i 1) E = lin (comb b e - s) i - coeff (Finsupp.single i 1) (comb n' e - S')`. Rewrite using `[hl, h1]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hl, h2, map_sub]`. Use `Submodule.sub_mem _ ?_ (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `hQL.2.1 i`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, h⟩`.

Rewrite using `[hcomb]`. Conclude with `Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)`. Rewrite using `[cS']`. Conclude with `mem_coeffIdeal.2 ⟨_, hm _, rfl⟩`. Establish `hcobE : ∀ α, ∃ y, coeff α (cob1 (up Q μ) E) = algebraMap B Q y ∧ a ∣ θ y`.

Introduce `α`. Establish `hej : ∀ j, coeff α (cob1 (up Q μ) (e j)) ∈ coeffIdeal (⊤ : Ideal B)` using `fun j => by`. Take `⟨y, hy, h⟩` from `(he j).2.2 α`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, h⟩`. Apply `hdiv` to reduce the goal to its premises.

Rewrite using `[hE, ← hL, map_sub, hL, hL, map_sub, hcobcomb]`. Use `Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j)) ?_` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS₁ α`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, h⟩`. Establish `h1 : cob1 (up Q μ) (comb b e - s) = cob1 (up Q μ) (comb n' e - S') + algebraMap B Q n • cob1 (up Q μ) E`.

Rewrite using `[← hL, hkey, map_add, map_smul]`. Both sides reduce to the same expression. Establish `h2 : algebraMap B Q n * coeff α (cob1 (up Q μ) E) = coeff α (cob1 (up Q μ) (comb b e - s)) - coeff α (cob1 (up Q μ) (comb n' e - S'))`. Rewrite using `[h1, map_add, coeff_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Use `Submodule.sub_mem _ ?_ ?_` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `hQL.2.2 α`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, h⟩`. Rewrite using `[← hL, map_sub, hL, hL, map_sub, hcobcomb]`.

Use `Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)) ?_` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS' α`. Conclude with `mem_coeffIdeal.2 ⟨y, hy, h⟩`. Establish `hupC : ∀ i, constantCoeff (up C (fun i => map θ (μ i)) i) = 0` using `fun i => by`. Simplify using `[up, hμ0 i]`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : C, u * algebraMap O C a = 1 := by`. Use `⟨algebraMap O C c * ↑hC.unit_p.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_right_comm, ← map_mul, mul_comm c a, ← hc, map_natCast]`. Conclude with `hC.unit_p.mul_val_inv`. Establish `hT : ∀ q : Q, (∃ y, q = algebraMap B Q y ∧ a ∣ θ y) → ∃ z, u * Θ q = algebraMap O C z ∧ Θ q = algebraMap O C (a * z)`.

Introduce and unpack `q ⟨y, rfl, z, hz⟩`. Use `⟨z, ?_, by rw [hΘ, hz]⟩` and prove the remaining obligations. Rewrite using `[hΘ, hz, map_mul, ← mul_assoc, hu, one_mul]`. Establish `hnat` using `map_formalGroupLawCoboundaryOne_eq θ Θ hΘ hμ0 E`. Establish `hE0 : coeff 0 E = 0`.

Rewrite using `[cE, ht0 0 rfl]`. Simplify using `[he0]`. Take `⟨F, hFd⟩ : ∃ F, F = u • map Θ E` from `⟨_, rfl⟩`. Establish `hQLF : QL (fun i => map θ (μ i)) ⊤ F`. Use `⟨?_, fun i => ?_, fun α => ?_⟩` and prove the remaining obligations.

Rewrite using `[hFd, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_map, hE0, map_zero, mul_zero]`. Take `⟨z, hz, -⟩` from `hT _ (hlinE i)`. Use `⟨z, trivial, ?_⟩` and prove the remaining obligations. Use `show coeff (Finsupp.single i 1) F = _`. Rewrite using `[hFd, coeff_smul, coeff_map, ← hl]`.

Conclude with `hz`. Take `⟨z, hz, -⟩` from `hT _ (hcobE α)`. Use `⟨z, trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[hFd, formalCoboundary_smul hupC, coeff_smul, ← hnat, coeff_map]`. Conclude with `hz`.

Establish `hQLΘ : QL (fun i => map θ (μ i)) ⊤ (map Θ E)`. Use `⟨?_, fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, hE0, map_zero]`. Take `⟨z, -, hz⟩` from `hT _ (hlinE i)`. Conclude with `⟨a * z, trivial, by show coeff (Finsupp.single i 1) (map Θ E) = _`.

Rewrite using `[coeff_map, ← hl]`. Conclude with `hz⟩`. Take `⟨z, -, hz⟩` from `hT _ (hcobE α)`. Conclude with `⟨a * z, trivial, by rw [← hnat, coeff_map]; exact hz⟩`. Take `⟨γ, hγ, -⟩` from `hB.2 F hQLF`.

Establish `hcΘ : ∀ (w : ι → O) α, coeff α (comb w (fun i => map Θ (e i))) = ∑ i, algebraMap O C (w i) * Θ (coeff α (e i))`. Introduce `w α`. Simplify using `only [comb, map_sum, coeff_smul, smul_eq_mul, coeff_map]`. Establish `hc1 : ∀ α, coeff α (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i))) = -algebraMap O C (θ (t α))`. Introduce `α`.

Rewrite using `[map_sub, coeff_map, cE, hcΘ, map_sub, map_sum]`. Simplify using `only [map_mul, hΘ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i)) = algebraMap O C a • (F - comb γ (fun i => map Θ (e i)))`. Rewrite using `[smul_sub, hFd, smul_smul, mul_comm, hu, one_smul, comb, comb, Finset.smul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, map_mul]`. Establish `hin2 : In (⊤ : Ideal O) (map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i)))`. Rewrite using `[h2]`.

Introduce `α`. Take `⟨w, -, hw⟩` from `hγ α`. Conclude with `⟨a * w, trivial, by rw [coeff_smul, hw, map_mul]⟩`. Establish `hin1 : In (⊤ : Ideal O) (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i)))` using `fun α => ⟨-θ (t α), trivial, by rw [hc1, map_neg]⟩`. Establish `heq` using `(hB.2 _ hQLΘ).unique hin1 hin2`.

Establish `hbN' : ∀ i, b i ∈ N'` using `fun i => by`. Rewrite using `[hβ i]`. Conclude with `N'.add_mem (hn' i) ((hn (β i)).2 ⟨γ i, congrFun heq i⟩)`. Use `⟨hbN', fun α => ⟨m α + t α * n, N'.add_mem (hm α) ((hn (t α)).2 ?_), hts α⟩⟩` and prove the remaining obligations. Take `⟨w, -, hw⟩` from `hγ α`.

Establish `h3` using `congrArg (coeff α) h2`. Rewrite `h3` using `[coeff_smul, hw, ← heq, hc1, ← map_mul]`. Establish `h4 : θ (t α) = -(a * w)`. Apply `hC.inj` to reduce the goal to its premises. Rewrite using `[map_neg, ← h3, neg_neg]`.

Conclude with `⟨-w, by rw [h4]; ring⟩`.
-/
theorem GlobalTheory.step_independent : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) → In N s → QL μ N' (comb b e - s) → (∀ i, b i ∈ N') ∧ In N' s := by
  intro p _ B O Q _ _ _ _ θ hF d μ hμ C _ _ hC Θ hΘ ι _ e he hB N' N hstep b s hb hs hQL
  obtain ⟨n, a, ⟨c, hc⟩, hN, hn⟩ := hstep
  have hμ0 := hμ.const
  have hup0 : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by simp [up, hμ0 i]
  have hdec : ∀ x ∈ N, ∃ m ∈ N', ∃ t : B, x = m + t * n := by
    intro x hx
    rw [hN, Submodule.mem_sup] at hx
    obtain ⟨m, hm, z, hz, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨m, hm, t, rfl⟩
  choose n' hn' β hβ using fun i => hdec (b i) (hb i)
  have hcomb : ∀ (w : ι → B) α, coeff α (comb w e) = ∑ i, algebraMap B Q (w i) * coeff α (e i) := by
    intro w α; simp only [comb, map_sum, coeff_smul, smul_eq_mul]
  have he0 : ∀ i, coeff 0 (e i) = 0 := fun i => by
    rw [coeff_zero_eq_constantCoeff_apply]; exact (he i).1
  have hs0 : coeff 0 s = 0 := by
    have h := hQL.1
    rw [← coeff_zero_eq_constantCoeff_apply, map_sub, hcomb] at h
    simpa [he0] using h
  have hsdec : ∀ α, ∃ m ∈ N', ∃ t : B, coeff α s = algebraMap B Q (m + t * n) ∧ (α = 0 → t = 0) := by
    intro α
    by_cases h0 : α = 0
    · exact ⟨0, N'.zero_mem, 0, by rw [h0, hs0]; simp, fun _ => rfl⟩
    · obtain ⟨x, hx, hxs⟩ := hs α
      obtain ⟨m, hm, t, rfl⟩ := hdec x hx
      exact ⟨m, hm, t, hxs, fun h => absurd h h0⟩
  choose m hm t hts ht0 using hsdec
  let S' : MvPowerSeries (Fin d) Q := map (algebraMap B Q) (fun α => m α)
  let S₁ : MvPowerSeries (Fin d) Q := map (algebraMap B Q) (fun α => t α)
  have cS' : ∀ α, coeff α S' = algebraMap B Q (m α) := fun α => by simp only [S', coeff_map]; rfl
  have cS₁ : ∀ α, coeff α S₁ = algebraMap B Q (t α) := fun α => by simp only [S₁, coeff_map]; rfl
  have hS' : In N' S' := fun α => ⟨m α, hm α, cS' α⟩
  have hS₁ : In (⊤ : Ideal B) S₁ := fun α => ⟨t α, trivial, cS₁ α⟩
  obtain ⟨E, hE⟩ : ∃ E, E = comb β e - S₁ := ⟨_, rfl⟩
  have cE : ∀ α, coeff α E = ∑ i, algebraMap B Q (β i) * coeff α (e i) - algebraMap B Q (t α) := by
    intro α; rw [hE, map_sub, hcomb, cS₁]
  have hkey : comb b e - s = (comb n' e - S') + algebraMap B Q n • E := by
    ext α
    rw [map_sub, map_add, map_sub, coeff_smul, cE, hcomb, hcomb, hts, cS']
    simp only [hβ, map_add, map_mul, add_mul, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
    ring_nf

  let L : MvPowerSeries (Fin d) Q →ₗ[Q] MvPowerSeries (Fin d ⊕ Fin d) Q :=
    { toFun := cob1 (up Q μ), map_add' := formalCoboundary_add hup0, map_smul' := formalCoboundary_smul hup0 }
  have hL : ∀ f, L f = cob1 (up Q μ) f := fun _ => rfl
  have hcobcomb : ∀ (w : ι → B) α, coeff α (cob1 (up Q μ) (comb w e)) =
      ∑ i, algebraMap B Q (w i) * coeff α (cob1 (up Q μ) (e i)) := by
    intro w α; rw [← hL]; unfold comb; rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, coeff_smul]; rfl
  have hdiv : ∀ q : Q, q ∈ coeffIdeal (⊤ : Ideal B) → algebraMap B Q n * q ∈ coeffIdeal N' →
      ∃ y, q = algebraMap B Q y ∧ a ∣ θ y := by
    intro q hq hnq
    obtain ⟨y, -, rfl⟩ := mem_coeffIdeal.1 hq
    obtain ⟨x, hx, hxy⟩ := mem_coeffIdeal.1 hnq
    refine ⟨y, rfl, (hn y).1 ?_⟩
    rw [← map_mul] at hxy
    rw [mul_comm, hF.inj hxy]; exact hx
  have hl : ∀ (f : MvPowerSeries (Fin d) Q) i, lin f i = coeff (Finsupp.single i 1) f := fun _ _ => rfl
  have hlinE : ∀ i, ∃ y, lin E i = algebraMap B Q y ∧ a ∣ θ y := by
    intro i
    have hej : ∀ j, coeff (Finsupp.single i 1) (e j) ∈ coeffIdeal (⊤ : Ideal B) := fun j => by
      obtain ⟨y, hy, h⟩ := (he j).2.1 i
      exact mem_coeffIdeal.2 ⟨y, hy, by rw [← hl]; exact h⟩
    apply hdiv
    · rw [hl, cE]
      exact Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j))
        (mem_coeffIdeal.2 ⟨_, trivial, rfl⟩)
    · have h1 := congrArg (coeff (Finsupp.single i 1)) hkey
      rw [map_add, coeff_smul] at h1
      have h2 : algebraMap B Q n * coeff (Finsupp.single i 1) E =
          lin (comb b e - s) i - coeff (Finsupp.single i 1) (comb n' e - S') := by
        rw [hl, h1]; ring
      rw [hl, h2, map_sub]
      refine Submodule.sub_mem _ ?_ (Submodule.sub_mem _ ?_ ?_)
      · obtain ⟨y, hy, h⟩ := hQL.2.1 i; exact mem_coeffIdeal.2 ⟨y, hy, h⟩
      · rw [hcomb]; exact Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)
      · rw [cS']; exact mem_coeffIdeal.2 ⟨_, hm _, rfl⟩
  have hcobE : ∀ α, ∃ y, coeff α (cob1 (up Q μ) E) = algebraMap B Q y ∧ a ∣ θ y := by
    intro α
    have hej : ∀ j, coeff α (cob1 (up Q μ) (e j)) ∈ coeffIdeal (⊤ : Ideal B) := fun j => by
      obtain ⟨y, hy, h⟩ := (he j).2.2 α
      exact mem_coeffIdeal.2 ⟨y, hy, h⟩
    apply hdiv
    · rw [hE, ← hL, map_sub, hL, hL, map_sub, hcobcomb]
      refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal' _ (hej j)) ?_
      obtain ⟨y, hy, h⟩ := coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS₁ α
      exact mem_coeffIdeal.2 ⟨y, hy, h⟩
    · have h1 : cob1 (up Q μ) (comb b e - s) =
          cob1 (up Q μ) (comb n' e - S') + algebraMap B Q n • cob1 (up Q μ) E := by
        rw [← hL, hkey, map_add, map_smul]; rfl
      have h2 : algebraMap B Q n * coeff α (cob1 (up Q μ) E) =
          coeff α (cob1 (up Q μ) (comb b e - s)) - coeff α (cob1 (up Q μ) (comb n' e - S')) := by
        rw [h1, map_add, coeff_smul]; ring
      rw [h2]
      refine Submodule.sub_mem _ ?_ ?_
      · obtain ⟨y, hy, h⟩ := hQL.2.2 α; exact mem_coeffIdeal.2 ⟨y, hy, h⟩
      · rw [← hL, map_sub, hL, hL, map_sub, hcobcomb]
        refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => mul_mem_coeffIdeal (hn' j) (hej j)) ?_
        obtain ⟨y, hy, h⟩ := coeffsInIdeal_formalGroupLawCoboundaryOne hμ0 hS' α
        exact mem_coeffIdeal.2 ⟨y, hy, h⟩
  have hupC : ∀ i, constantCoeff (up C (fun i => map θ (μ i)) i) = 0 := fun i => by
    simp [up, hμ0 i]
  obtain ⟨u, hu⟩ : ∃ u : C, u * algebraMap O C a = 1 := by
    refine ⟨algebraMap O C c * ↑hC.unit_p.unit⁻¹, ?_⟩
    rw [mul_right_comm, ← map_mul, mul_comm c a, ← hc, map_natCast]
    exact hC.unit_p.mul_val_inv
  have hT : ∀ q : Q, (∃ y, q = algebraMap B Q y ∧ a ∣ θ y) →
      ∃ z, u * Θ q = algebraMap O C z ∧ Θ q = algebraMap O C (a * z) := by
    rintro q ⟨y, rfl, z, hz⟩
    refine ⟨z, ?_, by rw [hΘ, hz]⟩
    rw [hΘ, hz, map_mul, ← mul_assoc, hu, one_mul]
  have hnat := map_formalGroupLawCoboundaryOne_eq θ Θ hΘ hμ0 E
  have hE0 : coeff 0 E = 0 := by
    rw [cE, ht0 0 rfl]; simp [he0]
  obtain ⟨F, hFd⟩ : ∃ F, F = u • map Θ E := ⟨_, rfl⟩
  have hQLF : QL (fun i => map θ (μ i)) ⊤ F := by
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [hFd, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_map, hE0, map_zero, mul_zero]
    · obtain ⟨z, hz, -⟩ := hT _ (hlinE i)
      refine ⟨z, trivial, ?_⟩
      show coeff (Finsupp.single i 1) F = _
      rw [hFd, coeff_smul, coeff_map, ← hl]; exact hz
    · obtain ⟨z, hz, -⟩ := hT _ (hcobE α)
      refine ⟨z, trivial, ?_⟩
      rw [hFd, formalCoboundary_smul hupC, coeff_smul, ← hnat, coeff_map]; exact hz
  have hQLΘ : QL (fun i => map θ (μ i)) ⊤ (map Θ E) := by
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hE0, map_zero]
    · obtain ⟨z, -, hz⟩ := hT _ (hlinE i)
      exact ⟨a * z, trivial, by
        show coeff (Finsupp.single i 1) (map Θ E) = _
        rw [coeff_map, ← hl]; exact hz⟩
    · obtain ⟨z, -, hz⟩ := hT _ (hcobE α)
      exact ⟨a * z, trivial, by rw [← hnat, coeff_map]; exact hz⟩
  obtain ⟨γ, hγ, -⟩ := hB.2 F hQLF
  have hcΘ : ∀ (w : ι → O) α, coeff α (comb w (fun i => map Θ (e i))) =
      ∑ i, algebraMap O C (w i) * Θ (coeff α (e i)) := by
    intro w α; simp only [comb, map_sum, coeff_smul, smul_eq_mul, coeff_map]
  have hc1 : ∀ α, coeff α (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i))) =
      -algebraMap O C (θ (t α)) := by
    intro α
    rw [map_sub, coeff_map, cE, hcΘ, map_sub, map_sum]
    simp only [map_mul, hΘ]; ring
  have h2 : map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i)) =
      algebraMap O C a • (F - comb γ (fun i => map Θ (e i))) := by
    rw [smul_sub, hFd, smul_smul, mul_comm, hu, one_smul, comb, comb, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, map_mul]
  have hin2 : In (⊤ : Ideal O) (map Θ E - comb (fun i => a * γ i) (fun i => map Θ (e i))) := by
    rw [h2]; intro α
    obtain ⟨w, -, hw⟩ := hγ α
    exact ⟨a * w, trivial, by rw [coeff_smul, hw, map_mul]⟩
  have hin1 : In (⊤ : Ideal O) (map Θ E - comb (fun i => θ (β i)) (fun i => map Θ (e i))) :=
    fun α => ⟨-θ (t α), trivial, by rw [hc1, map_neg]⟩
  have heq := (hB.2 _ hQLΘ).unique hin1 hin2
  have hbN' : ∀ i, b i ∈ N' := fun i => by
    rw [hβ i]; exact N'.add_mem (hn' i) ((hn (β i)).2 ⟨γ i, congrFun heq i⟩)
  refine ⟨hbN', fun α => ⟨m α + t α * n, N'.add_mem (hm α) ((hn (t α)).2 ?_), hts α⟩⟩
  obtain ⟨w, -, hw⟩ := hγ α
  have h3 := congrArg (coeff α) h2
  rw [coeff_smul, hw, ← heq, hc1, ← map_mul] at h3
  have h4 : θ (t α) = -(a * w) := by
    apply hC.inj; rw [map_neg, ← h3, neg_neg]
  exact ⟨-w, by rw [h4]; ring⟩
