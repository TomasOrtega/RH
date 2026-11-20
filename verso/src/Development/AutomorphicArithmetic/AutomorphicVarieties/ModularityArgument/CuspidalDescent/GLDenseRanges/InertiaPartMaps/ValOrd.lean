import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Hi.GlAx

namespace UpperTheory.V.Z.Desc.V0

section Avg

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Set `C : Subgroup A` to `B.subgroupOf A`. Use `haveI hfi : C.FiniteIndex := ⟨hfin⟩`. Use `haveI : Fintype (A ⧸ C) := Fintype.ofFinite _`. Set `F : A → W` to `fun a => (χ a)⁻¹ • ρ a w`. Establish `hF : ∀ x c : A, (c : G) ∈ B → F (x * c) = F x`.

Introduce `x c hc`. Simplify using `only [F, Subgroup.coe_mul, hm _ x.2 _ c.2, map_mul, Module.End.mul_apply, hw _ hc, hB _ c.2 hc, mul_one]`. Establish `hF' : ∀ x y : A, (x : A ⧸ C) = (y : A ⧸ C) → F x = F y`. Introduce `x y hxy`. Rewrite `hxy` using `[QuotientGroup.eq]`.

Use `hF x (x⁻¹ * y) (Subgroup.mem_subgroupOf.1 hxy)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left, eq_comm]`. Then use the resulting hypothesis. Establish `hρ : ∀ a (ha : a ∈ A) (x : A), ρ a (F x) = χ a • F (⟨a, ha⟩ * x)`. Introduce `a ha x`. Establish `h1` using `h0 a ha`.

Establish `h2` using `h0 _ x.2`. Simplify using `only [F, Subgroup.coe_mul, hm _ ha _ x.2, map_mul, Module.End.mul_apply, smul_smul, map_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `⟨∑ q : A ⧸ C, F q.out, ?_, fun a ha => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hP _ q.out.2)`. Establish `e : ∀ q : A ⧸ C, F (⟨a, ha⟩ * q.out) = F ((⟨a, ha⟩ : A) • q).out`. Introduce `q`. Apply `hF'` to reduce the goal to its premises. Rewrite using `[QuotientGroup.out_eq']`.

Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[map_sum, Finset.smul_sum]`. Simplify using `only [hρ a ha, e]`. Conclude with `Equiv.sum_comp (MulAction.toPerm (⟨a, ha⟩ : A)) (fun q : A ⧸ C => χ a • F q.out)`.

Establish `hq : ∀ q : A ⧸ C, l (F q.out) = l w`. Introduce `q`. Simplify using `only [F, map_smul, smul_eq_mul, hl _ q.out.2]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (h0 _ q.out.2), one_mul]`. Rewrite using `[map_sum]`.

Simplify using `only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 1`. Simplify using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, C]`.
-/
private theorem avg (ρ : Representation ℂ G W) (A B : Subgroup G) (hfin : B.relIndex A ≠ 0) (χ : G → ℂ)
    (hm : ∀ a ∈ A, ∀ b ∈ A, χ (a * b) = χ a * χ b) (h0 : ∀ a ∈ A, χ a ≠ 0) (hB : ∀ b ∈ A, b ∈ B → χ b = 1)
    (w : W) (hw : ∀ b ∈ B, ρ b w = w) (l : W →ₗ[ℂ] ℂ) (hl : ∀ a ∈ A, l (ρ a w) = χ a * l w)
    (P : Submodule ℂ W) (hP : ∀ a ∈ A, ρ a w ∈ P) :
    ∃ w' ∈ P, (∀ a ∈ A, ρ a w' = χ a • w') ∧ l w' = (B.relIndex A : ℂ) * l w := by
  classical
  let C : Subgroup A := B.subgroupOf A
  haveI hfi : C.FiniteIndex := ⟨hfin⟩
  haveI : Fintype (A ⧸ C) := Fintype.ofFinite _
  let F : A → W := fun a => (χ a)⁻¹ • ρ a w
  have hF : ∀ x c : A, (c : G) ∈ B → F (x * c) = F x := by
    intro x c hc
    simp only [F, Subgroup.coe_mul, hm _ x.2 _ c.2, map_mul, Module.End.mul_apply, hw _ hc, hB _ c.2 hc, mul_one]
  have hF' : ∀ x y : A, (x : A ⧸ C) = (y : A ⧸ C) → F x = F y := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    have := hF x (x⁻¹ * y) (Subgroup.mem_subgroupOf.1 hxy)
    rwa [mul_inv_cancel_left, eq_comm] at this
  have hρ : ∀ a (ha : a ∈ A) (x : A), ρ a (F x) = χ a • F (⟨a, ha⟩ * x) := by
    intro a ha x
    have h1 := h0 a ha
    have h2 := h0 _ x.2
    simp only [F, Subgroup.coe_mul, hm _ ha _ x.2, map_mul, Module.End.mul_apply, smul_smul, map_smul]
    congr 1
    field_simp
  refine ⟨∑ q : A ⧸ C, F q.out, ?_, fun a ha => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hP _ q.out.2)
  · have e : ∀ q : A ⧸ C, F (⟨a, ha⟩ * q.out) = F ((⟨a, ha⟩ : A) • q).out := by
      intro q
      apply hF'
      rw [QuotientGroup.out_eq']
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [map_sum, Finset.smul_sum]
    simp only [hρ a ha, e]
    exact Equiv.sum_comp (MulAction.toPerm (⟨a, ha⟩ : A)) (fun q : A ⧸ C => χ a • F q.out)
  · have hq : ∀ q : A ⧸ C, l (F q.out) = l w := by
      intro q
      simp only [F, map_smul, smul_eq_mul, hl _ q.out.2]
      rw [← mul_assoc, inv_mul_cancel₀ (h0 _ q.out.2), one_mul]
    rw [map_sum]
    simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, C]

end Avg

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv in
/- English proof (translation)
The claim follows from `exists_unipB_mul_diagT_mul_KO k n g`.
-/
private theorem iwasawa (g : GL (Fin n) k) :
    ∃ u ∈ unipB k (Fin n), ∃ d : Fin n → kˣ, ∃ κ ∈ KO k (Fin n), g = u * diagT k (Fin n) d * κ :=
  exists_unipB_mul_diagT_mul_KO k n g

/- English proof (translation)
Establish `h` using `val_div_ord x`. Rewrite `h` using `[Units.val_div_eq_div_val, map_div₀, val_zpow, div_eq_one_iff_eq]`. Conclude with `h`. Conclude with `(zpow_pos unif_pos _).ne'`.
-/
private theorem val_ord' (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, val_zpow, div_eq_one_iff_eq] at h
  · exact h
  · exact (zpow_pos unif_pos _).ne'

/- English proof (translation)
Take `⟨y, rfl⟩` from `hg`. Take `⟨z, hz, rfl⟩` from `hx`. Conclude with `⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩`.
-/
private theorem Kc_conj' {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g * x * g⁻¹ ∈ Kc k n 1 := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩

/- English proof (translation)
Conclude with `inferInstanceAs (IsLocalRing (valuation k).valuationSubring)`.
-/
private theorem locO : IsLocalRing 𝒪[k] := by
  exact inferInstanceAs (IsLocalRing (valuation k).valuationSubring)
attribute [local instance] locO

/- English proof (translation)
Take `⟨g0, hg0, rfl⟩` from `hg`. Establish `hI : 𝓂[k] ^ 1 ≤ IsLocalRing.maximalIdeal 𝒪[k]` using `by simp`. Take `⟨u, hu, t, lw, hlw, ht1, hl1, hfac⟩` from `udl _ hI g0 hg0`. Establish `hmap : ∀ (h : GL (Fin n) 𝒪[k]) (i j : Fin n), (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h : Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j)` using `fun h i j => by simp`. Establish `hdiag : GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin n) t) = diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i))`.

Use extensionality with `i j`. Simplify using `[val_diagT, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hu1 : GeneralLinearGroup.map (Ideal.Quotient.mk (𝓂[k] ^ 1)) u = 1`. Establish `hu' : u = g0 * lw⁻¹ * (diagT 𝒪[k] (Fin n) t)⁻¹`.

Rewrite using `[hfac]`. Use `group`. Rewrite using `[hu', map_mul, map_mul, map_inv, map_inv, ht1, hl1, hg0]`. Simplify using the standard rewrite rules. Rewrite `hlw` using `[mem_low]`.

Use `⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ?_, ⟨u, hu1, rfl⟩, fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i), ⟨diagT 𝒪[k] (Fin n) t, ht1, hdiag⟩, GeneralLinearGroup.map (algebraMap 𝒪[k] k) lw, ⟨?_, ⟨lw, hl1, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[mem_unipB]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hmap, hu.1 i j hij, map_zero]`. Rewrite using `[hmap, hu.2 i, map_one]`.

Use `mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hmap, hlw.1 i j hij, map_zero]`. Rewrite using `[hmap, hlw.2 i, map_one]`. Rewrite using `[hfac, map_mul, map_mul, hdiag]`.
-/
private theorem iwahori {g : GL (Fin n) k} (hg : g ∈ Kc k n 1) :
    ∃ x ∈ unipB k (Fin n), x ∈ Kc k n 1 ∧ ∃ s : Fin n → kˣ, diagT k (Fin n) s ∈ Kc k n 1 ∧
      ∃ y ∈ (glData k n).Nm 0, g = x * diagT k (Fin n) s * y := by
  obtain ⟨g0, hg0, rfl⟩ := hg
  have hI : 𝓂[k] ^ 1 ≤ IsLocalRing.maximalIdeal 𝒪[k] := by simp
  obtain ⟨u, hu, t, lw, hlw, ht1, hl1, hfac⟩ := udl _ hI g0 hg0
  have hmap : ∀ (h : GL (Fin n) 𝒪[k]) (i j : Fin n),
      (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h : Matrix (Fin n) (Fin n) k) i j =
        algebraMap 𝒪[k] k ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := fun h i j => by simp
  have hdiag : GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin n) t) =
      diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i)) := by
    ext i j
    simp [val_diagT, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hu1 : GeneralLinearGroup.map (Ideal.Quotient.mk (𝓂[k] ^ 1)) u = 1 := by
    have hu' : u = g0 * lw⁻¹ * (diagT 𝒪[k] (Fin n) t)⁻¹ := by
      rw [hfac]
      group
    rw [hu', map_mul, map_mul, map_inv, map_inv, ht1, hl1, hg0]
    simp
  rw [mem_low] at hlw
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ?_, ⟨u, hu1, rfl⟩,
    fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i), ⟨diagT 𝒪[k] (Fin n) t, ht1, hdiag⟩,
    GeneralLinearGroup.map (algebraMap 𝒪[k] k) lw, ⟨?_, ⟨lw, hl1, rfl⟩⟩, ?_⟩
  · rw [mem_unipB] at hu ⊢
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmap, hu.1 i j hij, map_zero]
    · rw [hmap, hu.2 i, map_one]
  · refine mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmap, hlw.1 i j hij, map_zero]
    · rw [hmap, hlw.2 i, map_one]
  · rw [hfac, map_mul, map_mul, hdiag]

private def el (a b : Fin n) (h : a ≠ b) (y : k) : GL (Fin n) k :=
  ⟨transvection a b y, transvection a b (-y),
    by rw [transvection_mul_transvection_same _ _ h]; simp, by rw [transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem el_apply (a b : Fin n) (h : a ≠ b) (y : k) (p q : Fin n) :
    (el a b h y).val p q = (1 : Matrix (Fin n) (Fin n) k) p q + Matrix.single a b y p q := rfl

/- English proof (translation)
Rewrite using `[mem_unipB]`. Use `⟨fun i j hji => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[el_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply] split_ifs with hh`. Break down `hh with ⟨rfl, rfl⟩` into its components or cases. Conclude with `absurd hji (not_lt.2 h.le)`.

Simplify using the standard rewrite rules. Rewrite using `[el_apply, Matrix.one_apply_eq, Matrix.single_apply] split_ifs with hh`. Break down `hh with ⟨rfl, rfl⟩` into its components or cases. Conclude with `absurd h (lt_irrefl _)`. Simplify using the standard rewrite rules.
-/
private theorem el_unip {a b : Fin n} (h : a < b) (y : k) : el a b h.ne y ∈ unipB k (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [el_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
    split_ifs with hh
    · rcases hh with ⟨rfl, rfl⟩
      exact absurd hji (not_lt.2 h.le)
    · simp
  · rw [el_apply, Matrix.one_apply_eq, Matrix.single_apply]
    split_ifs with hh
    · rcases hh with ⟨rfl, rfl⟩
      exact absurd h (lt_irrefl _)
    · simp

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.sub_apply, el_apply, add_sub_cancel_left, Matrix.single_apply]`. Use `split_ifs`. Conclude with `hy`. Rewrite using `[map_zero]`.

Conclude with `zero_le'`.
-/
private theorem el_bd {a b : Fin n} (h : a ≠ b) {y : k} (hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ)) :
    Bd ((1 : ℕ) : ℤ) (el a b h y) := by
  intro i j
  rw [Matrix.sub_apply, el_apply, add_sub_cancel_left, Matrix.single_apply]
  split_ifs
  · exact hy
  · rw [map_zero]
    exact zero_le'

/- English proof (translation)
Establish `hinv : (el a b h y)⁻¹ = el a b h (-y)` using `Units.ext rfl`. Use `mem_Kc.2 ⟨el_bd h hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv]`. Conclude with `el_bd h (by rwa [Valuation.map_neg])`.
-/
private theorem el_Kc {a b : Fin n} (h : a ≠ b) {y : k} (hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ)) :
    el a b h y ∈ Kc k n 1 := by
  have hinv : (el a b h y)⁻¹ = el a b h (-y) := Units.ext rfl
  refine mem_Kc.2 ⟨el_bd h hy, ?_⟩
  rw [hinv]
  exact el_bd h (by rwa [Valuation.map_neg])

/- English proof (translation)
Unfold `chr`. Use `congr 2`. Rewrite using `[Finset.sum_eq_single (a, b)]`. Rewrite using `[conj_apply, el_apply, Matrix.one_apply_ne h, Matrix.single_apply_same, zero_add]`. Introduce and unpack `⟨p, q⟩ hpq hne`.

Simplify using `only [Finset.mem_filter] at hpq`. Establish `hpq' : p ≠ q` using `fun e => by subst e; omega`. Establish `hn : ¬ (a = p ∧ b = q)` using `fun ⟨e1, e2⟩ => hne (by rw [e1, e2])`. Rewrite using `[conj_apply, el_apply, Matrix.one_apply_ne hpq', Matrix.single_apply, if_neg hn]`. Simplify using the standard rewrite rules.

Introduce `hab'`. Conclude with `absurd (Finset.mem_filter.2 ⟨Finset.mem_univ (a, b), hab⟩) hab'`.
-/
private theorem chr_el {a b : Fin n} (hab : (b : ℕ) = a + 1) (h : a ≠ b) (ψ : AddChar k Circle) (t : Fin n → k)
    (d : Fin n → kˣ) (y : k) :
    chr ψ t (diagT k (Fin n) d * el a b h y * (diagT k (Fin n) d)⁻¹) = (ψ (t a * ((d a : k) * y * ((d b)⁻¹ : kˣ))) : ℂ) := by
  unfold chr
  congr 2
  rw [Finset.sum_eq_single (a, b)]
  · rw [conj_apply, el_apply, Matrix.one_apply_ne h, Matrix.single_apply_same, zero_add]
  · rintro ⟨p, q⟩ hpq hne
    simp only [Finset.mem_filter] at hpq
    have hpq' : p ≠ q := fun e => by subst e; omega
    have hn : ¬ (a = p ∧ b = q) := fun ⟨e1, e2⟩ => hne (by rw [e1, e2])
    rw [conj_apply, el_apply, Matrix.one_apply_ne hpq', Matrix.single_apply, if_neg hn]
    simp
  · intro hab'
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ (a, b), hab⟩) hab'

/- English proof (translation)
Unfold `chr`. Establish `hb` using `(mem_Kc.1 hx).1`. Establish `hlt : valuation k (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1), t p.1 * (x : Matrix (Fin n) (Fin n) k) p.1 p.2) < 1`. Use `Valuation.map_sum_lt _ one_ne_zero fun p hp => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter] at hp`.

Establish `hne : p.1 ≠ p.2` using `fun e => by rw [e] at hp; omega`. Establish `hxe : (x : Matrix (Fin n) (Fin n) k) p.1 p.2 = ((x : Matrix (Fin n) (Fin n) k) - 1) p.1 p.2`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Rewrite using `[map_mul, ht, one_mul, hxe]`. Use `lt_of_le_of_lt (hb p.1 p.2) ?_` and prove the remaining obligations.

Simplify using `using ValuativeRel.uniformizer_lt_one (R := k)`. Rewrite using `[hψ _ hlt]`. Simplify using the standard rewrite rules.
-/
private theorem chr_one {ψ : AddChar k Circle} {t : Fin n → k} (hψ : ∀ x : k, valuation k x < 1 → ψ x = 1)
    (ht : ∀ i, valuation k (t i) = 1) {x : GL (Fin n) k} (hx : x ∈ Kc k n 1) : chr ψ t x = 1 := by
  unfold chr
  have hb := (mem_Kc.1 hx).1
  have hlt : valuation k (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
      t p.1 * (x : Matrix (Fin n) (Fin n) k) p.1 p.2) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    have hne : p.1 ≠ p.2 := fun e => by rw [e] at hp; omega
    have hxe : (x : Matrix (Fin n) (Fin n) k) p.1 p.2 = ((x : Matrix (Fin n) (Fin n) k) - 1) p.1 p.2 := by
      rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [map_mul, ht, one_mul, hxe]
    refine lt_of_le_of_lt (hb p.1 p.2) ?_
    simpa using ValuativeRel.uniformizer_lt_one (R := k)
  rw [hψ _ hlt]
  simp

/- English proof (translation)
Take `⟨x0, hx0, hψx0⟩` from `hnt`. Break down `n with _ | m` into its components or cases. Introduce `i`. Conclude with `i.elim0`. Use `Fin.antitone_iff_succ_le.2 fun i => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hab : i.castSucc < i.succ` using `Fin.castSucc_lt_succ`. Establish `habn : ((i.succ : Fin (m + 1)) : ℕ) = (i.castSucc : Fin (m + 1)) + 1` using `by simp`. Establish `hta : t i.castSucc ≠ 0` using `fun e => by`.

Use `ht i.castSucc` as an intermediate fact. Rewrite `this` using `[e, map_zero]`. Conclude with `zero_ne_one this`. Use `set y : k := x0 * (d i.succ : k) / (t i.castSucc * (d i.castSucc : k)) with hydef`. Establish `hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ)`.

Establish `hu : uniformizer k ≠ 0` using `unif_pos.ne'`. Rewrite using `[hydef, map_div₀, map_mul, map_mul, ht, one_mul, val_ord', val_ord', mul_div_assoc, ← zpow_sub₀ hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `zpow_le (by push_cast; omega)`.

Establish `key` using `H _ (el_unip hab y) (el_Kc hab.ne hy)`. Rewrite `key` using `[chr_el habn hab.ne ψ t d y]`. Establish `hval : t i.castSucc * ((d i.castSucc : k) * y * (((d i.succ)⁻¹ : kˣ) : k)) = x0`. Rewrite using `[hydef, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.

Rewrite `key` using `[hval]`. Conclude with `hψx0 (Circle.coe_injective (key.trans Circle.coe_one.symm))`.
-/
private theorem dom {ψ : AddChar k Circle} {t : Fin n → k} (hnt : ∃ x : k, valuation k x ≤ 1 ∧ ψ x ≠ 1)
    (ht : ∀ i, valuation k (t i) = 1) (d : Fin n → kˣ)
    (H : ∀ x ∈ unipB k (Fin n), x ∈ Kc k n 1 →
      chr ψ t (diagT k (Fin n) d * x * (diagT k (Fin n) d)⁻¹) = 1) :
    Antitone fun i => ord k (d i) := by
  obtain ⟨x0, hx0, hψx0⟩ := hnt
  rcases n with _ | m
  · intro i
    exact i.elim0
  refine Fin.antitone_iff_succ_le.2 fun i => ?_
  by_contra hlt
  push_neg at hlt
  have hab : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have habn : ((i.succ : Fin (m + 1)) : ℕ) = (i.castSucc : Fin (m + 1)) + 1 := by simp
  have hta : t i.castSucc ≠ 0 := fun e => by
    have := ht i.castSucc
    rw [e, map_zero] at this
    exact zero_ne_one this
  set y : k := x0 * (d i.succ : k) / (t i.castSucc * (d i.castSucc : k)) with hydef
  have hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ) := by
    have hu : uniformizer k ≠ 0 := unif_pos.ne'
    rw [hydef, map_div₀, map_mul, map_mul, ht, one_mul, val_ord', val_ord', mul_div_assoc, ← zpow_sub₀ hu]
    calc valuation k x0 * uniformizer k ^ (ord k (d i.succ) - ord k (d i.castSucc))
        ≤ 1 * uniformizer k ^ (ord k (d i.succ) - ord k (d i.castSucc)) := by gcongr
      _ ≤ _ := by
        rw [one_mul]
        exact zpow_le (by push_cast; omega)
  have key := H _ (el_unip hab y) (el_Kc hab.ne hy)
  rw [chr_el habn hab.ne ψ t d y] at key
  have hval : t i.castSucc * ((d i.castSucc : k) * y * (((d i.succ)⁻¹ : kˣ) : k)) = x0 := by
    rw [hydef, Units.val_inv_eq_inv_val]
    field_simp
  rw [hval] at key
  exact hψx0 (Circle.coe_injective (key.trans Circle.coe_one.symm))

end Loc

/- English proof (translation)
Rewrite `ha`, `hb` using `[mem_unipB]`. Unfold `chr`. Establish `key : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1), t p.1 * ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2 = t p.1 * (a : Matrix (Fin n) (Fin n) k) p.1 p.2 + t p.1 * (b : Matrix (Fin n) (Fin n) k) p.1 p.2`. Introduce and unpack `⟨i, j⟩ hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Establish `hij : i ≠ j` using `fun e => by rw [e] at hp; omega`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add i j hij]`. Rewrite using `[ha.2 i, hb.2 j]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `m ⟨hmi, hmj⟩`.

Break down `lt_or_gt_of_ne hmi with h | h` into its components or cases. Rewrite using `[ha.1 i m h, zero_mul]`. Establish `hjm : j < m`. Rewrite `h`, the goal using `[Fin.lt_def]`. Use `Fin.val_ne_of_ne hmj` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hb.1 m j hjm, mul_zero]`. Rewrite using `[Finset.sum_congr rfl key, Finset.sum_add_distrib, AddChar.map_add_eq_mul, Circle.coe_mul]`.
-/
private theorem isoNe_lemma {k : Type} [Field k] {n : ℕ} (ψ : AddChar k Circle) (t : Fin n → k)
    {a b : GL (Fin n) k} (ha : a ∈ unipB k (Fin n)) (hb : b ∈ unipB k (Fin n)) :
    chr ψ t (a * b) = chr ψ t a * chr ψ t b := by
  rw [mem_unipB] at ha hb
  unfold chr
  have key : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
      t p.1 * ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2 =
        t p.1 * (a : Matrix (Fin n) (Fin n) k) p.1 p.2 + t p.1 * (b : Matrix (Fin n) (Fin n) k) p.1 p.2 := by
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hij : i ≠ j := fun e => by rw [e] at hp; omega
    rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [ha.2 i, hb.2 j]
      ring
    · rintro m ⟨hmi, hmj⟩
      rcases lt_or_gt_of_ne hmi with h | h
      · rw [ha.1 i m h, zero_mul]
      · have hjm : j < m := by
          rw [Fin.lt_def] at h ⊢
          have := Fin.val_ne_of_ne hmj
          omega
        rw [hb.1 m j hjm, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, AddChar.map_add_eq_mul, Circle.coe_mul]

/- English proof (translation)
Introduce `i j`. Establish `hu : uniformizer k ≠ 0` using `unif_pos.ne'`. Establish `key : ((diagT k (Fin n) d⁻¹ * h * (diagT k (Fin n) d⁻¹)⁻¹ : GL (Fin n) k) - 1 : Matrix (Fin n) (Fin n) k) i j = ((d i : k))⁻¹ * ((h : Matrix (Fin n) (Fin n) k) - 1) i j * (d j : k)`. Rewrite using `[Matrix.sub_apply, conj_apply, Matrix.sub_apply]`. Simplify using `only [Pi.inv_apply, inv_inv, Units.val_inv_eq_inv_val]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Use `(d i).ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Matrix.one_apply_ne hij]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, map_mul, map_mul, map_inv₀, val_ord', val_ord', ← _root_.zpow_neg]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hh i j`.

Use `_ = uniformizer k ^ ((c : ℤ) + ord k (d j) - ord k (d i)) := by`. Rewrite using `[← zpow_add₀ hu, ← zpow_add₀ hu]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := zpow_le (by push_cast; linarith [hc i j])`.
-/
private theorem isoNe_lemma_2 {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d : Fin n → kˣ) (c : ℕ) (hc : ∀ i j : Fin n, 1 ≤ (c : ℤ) + ord k (d j) - ord k (d i))
    {h : GL (Fin n) k} (hh : Bd (c : ℤ) h) :
    Bd ((1 : ℕ) : ℤ) (diagT k (Fin n) d⁻¹ * h * (diagT k (Fin n) d⁻¹)⁻¹) := by
  intro i j
  have hu : uniformizer k ≠ 0 := unif_pos.ne'
  have key : ((diagT k (Fin n) d⁻¹ * h * (diagT k (Fin n) d⁻¹)⁻¹ : GL (Fin n) k) - 1 : Matrix (Fin n) (Fin n) k) i j =
      ((d i : k))⁻¹ * ((h : Matrix (Fin n) (Fin n) k) - 1) i j * (d j : k) := by
    rw [Matrix.sub_apply, conj_apply, Matrix.sub_apply]
    simp only [Pi.inv_apply, inv_inv, Units.val_inv_eq_inv_val]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      have := (d i).ne_zero
      field_simp
    · rw [Matrix.one_apply_ne hij]
      ring
  rw [key, map_mul, map_mul, map_inv₀, val_ord', val_ord', ← _root_.zpow_neg]
  calc uniformizer k ^ (-ord k (d i)) * valuation k (((h : Matrix (Fin n) (Fin n) k) - 1) i j) * uniformizer k ^ ord k (d j)
      ≤ uniformizer k ^ (-ord k (d i)) * uniformizer k ^ (c : ℤ) * uniformizer k ^ ord k (d j) := by
        gcongr
        exact hh i j
    _ = uniformizer k ^ ((c : ℤ) + ord k (d j) - ord k (d i)) := by
        rw [← zpow_add₀ hu, ← zpow_add₀ hu]
        congr 1
        ring
    _ ≤ _ := zpow_le (by push_cast; linarith [hc i j])

/- English proof (translation)
Unfold `IsoNe`. Introduce `k _ _ _ _ n W _ _ τ _ ψ t l hψ ht hK hfix`. Take `⟨_, hψ1, hnt⟩` from `hψ`. Take `⟨hequiv, hnd⟩` from `hK`. Establish `memfix : ∀ (K : Subgroup (GL (Fin n) k)) (v : W), v ∈ fixd τ K ↔ ∀ g ∈ K, τ g v = v` using `fun _ _ => Iff.rfl`.

Establish `hconj : ∀ g ∈ KO k (Fin n), ∀ v ∈ fixd τ (Kc k n 1), τ g v ∈ fixd τ (Kc k n 1)`. Introduce `g hg v hv`. Use `(memfix _ _).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ Kc k n 1` using `Kc_conj' (inv_mem hg) hx`. Establish `e : x * g = g * (g⁻¹ * x * g⁻¹⁻¹)` using `by group`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hv _ h1]`. Take `⟨w0, hw0, hw0ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hfix`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, l (τ p w0) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hw0ne (hnd w0 fun p _ => hcon p)`. Take `⟨u, hu, d, κ, hκ, rfl⟩` from `iwasawa p`. Use `set D := diagT k (Fin n) d with hD`. Establish `hw1` using `hconj κ hκ w0 hw0`. Use `set w1 := τ κ w0 with hw1def`.

Establish `hL : l (τ D w1) ≠ 0`. Introduce `h0`. Apply `hp` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hequiv u hu, h0, mul_zero]`. Establish `hdom : Antitone fun i => ord k (d i)`.

Use `dom hnt ht d fun x hxu hxK => ?_` and prove the remaining obligations. Establish `hx1 : τ x w1 = w1` using `(memfix _ _).1 hw1 x hxK`. Establish `e2 : D * x * D⁻¹ * D = D * x` using `by group`. Establish `e3 : τ (D * x * D⁻¹) (τ D w1) = τ D w1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e2, map_mul, Module.End.mul_apply, hx1]`.

Establish `e : l (τ D w1) = chr ψ t (D * x * D⁻¹) * l (τ D w1)`. Rewrite using `[← hequiv _ (conj_up d hxu), e3]`. Conclude with `mul_right_cancel₀ hL (e.symm.trans (one_mul _).symm)`. Set `M : ℕ` to `∑ i, (ord k (d i)).natAbs`. Establish `hMi : ∀ i, -(M : ℤ) ≤ ord k (d i) ∧ ord k (d i) ≤ M`.

Introduce `i`. Establish `h1 : (ord k (d i)).natAbs ≤ M` using `Finset.single_le_sum (f := fun i => (ord k (d i)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Establish `h2 : |ord k (d i)| ≤ (M : ℤ)`. Rewrite using `[Int.abs_eq_natAbs]`. Conclude with `h1` after adjusting the coercions.

Conclude with `abs_le.1 h2`. Establish `hc : ∀ i j : Fin n, 1 ≤ ((2 * M + 1 : ℕ) : ℤ) + ord k (d j) - ord k (d i)`. Introduce `i j`. Establish `a1` using `hMi i`. Establish `a2` using `hMi j`.

Use `push_cast`. Combine the linear relations using `[a1.1, a1.2, a2.1, a2.2]`. Set `Bg : Subgroup (GL (Fin n) k)` to `(Kc k n 1).comap (MulAut.conj D⁻¹).toMonoidHom`. Establish `hDinv : D⁻¹ = diagT k (Fin n) d⁻¹` using `(map_inv _ d).symm`. Establish `hBmem : ∀ g, g ∈ Bg ↔ D⁻¹ * g * D⁻¹⁻¹ ∈ Kc k n 1` using `fun g => Iff.rfl`.

Establish `hle : Kc k n (2 * M + 1) ≤ Bg`. Introduce `g hg`. Rewrite using `[hBmem, mem_Kc]`. Take `⟨hg1, hg2⟩` from `mem_Kc.1 hg`. Rewrite using `[hDinv]`.

Use `⟨isoNe_lemma_2 d _ hc hg1, ?_⟩` and prove the remaining obligations. Establish `e : (diagT k (Fin n) d⁻¹ * g * (diagT k (Fin n) d⁻¹)⁻¹)⁻¹ = diagT k (Fin n) d⁻¹ * g⁻¹ * (diagT k (Fin n) d⁻¹)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `isoNe_lemma_2 d _ hc hg2`. Establish `hfin1 : Bg.relIndex (Kc k n 1) ≠ 0` using `ne_zero_of_dvd_ne_zero (Kc_index (2 * M + 1) (Kc_le 1)) (Subgroup.relIndex_dvd_of_le_left _ hle)`.

Establish `hw2 : ∀ b ∈ Bg, τ b (τ D w1) = τ D w1`. Introduce `b hb`. Establish `hb' : D⁻¹ * b * D⁻¹⁻¹ ∈ Kc k n 1` using `(hBmem b).1 hb`. Establish `e : b * D = D * (D⁻¹ * b * D⁻¹⁻¹)` using `by group`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hb']`.

Establish `hl1 : ∀ a ∈ Kc k n 1, l (τ a (τ D w1)) = (fun _ => (1 : ℂ)) a * l (τ D w1)`. Introduce `a ha`. Take `⟨x, hxu, hxK, s, hsK, y, hy, rfl⟩` from `iwahori ha`. Establish `hyc : D⁻¹ * y * D⁻¹⁻¹ ∈ Kc k n 1`. Rewrite using `[hDinv]`.

Establish `hN` using `conj_Nm (t := d⁻¹) (a := fun i => -ord k (d i)) ?_ (c := 0) (c' := 0) ?_ hy`. Conclude with `(Subgroup.mem_inf.1 hN).2`. Introduce `i`. Rewrite using `[Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, val_ord', _root_.zpow_neg]`. Introduce `i j hji`.

Establish `h' : ord k (d i) ≤ ord k (d j)` using `hdom hji.le`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy' : τ y (τ D w1) = τ D w1` using `hw2 y ((hBmem y).2 hyc)`. Establish `hsD : diagT k (Fin n) s * D = D * diagT k (Fin n) s`.

Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Establish `hs' : τ (diagT k (Fin n) s) (τ D w1) = τ D w1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hsD, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hsK]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy', hs', hequiv x hxu, chr_one hψ1 ht hxK]`. Take `⟨w3, -, hw3, hlw3⟩` from `avg τ (Kc k n 1) Bg hfin1 (fun _ => (1 : ℂ)) (by simp) (by simp) (by simp) (τ D w1) hw2 l hl1 ⊤ (by simp)`.

Establish `hw3fix : w3 ∈ fixd τ (Kc k n 1)` using `(memfix _ _).2 fun g hg => by`. Rewrite using `[hw3 g hg]`. Simplify using the standard rewrite rules. Take `⟨w', hw'P, hw'eig, hlw'⟩` from `avg τ (unipB k (Fin n) ⊓ KO k (Fin n)) (Kc k n 1) (Kc_index 1 inf_le_right) (chr ψ t) (fun a ha b hb => isoNe_lemma ψ t (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1) (fun a _ => by unfold chr; simp) (fun b _ hb => chr_one hψ1 ht hb) w3 (fun b hb => (memfix _ _).1 hw3fix b …`. Rewrite using `[Submodule.ne_bot_iff]`.

Use `⟨w', ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_inf.2 ⟨hw'P, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`. Introduce and unpack `v ⟨hvu, hvK⟩`. Rewrite using `[Module.End.mem_eigenspace_iff]`.

Conclude with `hw'eig v (Subgroup.mem_inf.2 ⟨hvu, hvK⟩)`. Introduce `h0`. Rewrite `hlw'` using `[h0, map_zero, hlw3]`. Establish `hi2` using `Kc_index (n := n) (k := k) 1 (H := unipB k (Fin n) ⊓ KO k (Fin n)) inf_le_right`. Conclude with `hL (by simpa [hfin1, hi2] using hlw'.symm)`.
-/
theorem isoNe : IsoNe := by
  unfold IsoNe
  intro k _ _ _ _ n W _ _ τ _ ψ t l hψ ht hK hfix
  obtain ⟨_, hψ1, hnt⟩ := hψ
  obtain ⟨hequiv, hnd⟩ := hK
  have memfix : ∀ (K : Subgroup (GL (Fin n) k)) (v : W), v ∈ fixd τ K ↔ ∀ g ∈ K, τ g v = v :=
    fun _ _ => Iff.rfl
  have hconj : ∀ g ∈ KO k (Fin n), ∀ v ∈ fixd τ (Kc k n 1), τ g v ∈ fixd τ (Kc k n 1) := by
    intro g hg v hv
    refine (memfix _ _).2 fun x hx => ?_
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ Kc k n 1 := Kc_conj' (inv_mem hg) hx
    have e : x * g = g * (g⁻¹ * x * g⁻¹⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hv _ h1]
  obtain ⟨w0, hw0, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  obtain ⟨p, hp⟩ : ∃ p, l (τ p w0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0ne (hnd w0 fun p _ => hcon p)
  obtain ⟨u, hu, d, κ, hκ, rfl⟩ := iwasawa p
  set D := diagT k (Fin n) d with hD
  have hw1 := hconj κ hκ w0 hw0
  set w1 := τ κ w0 with hw1def
  have hL : l (τ D w1) ≠ 0 := by
    intro h0
    apply hp
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hequiv u hu, h0, mul_zero]
  have hdom : Antitone fun i => ord k (d i) := by
    refine dom hnt ht d fun x hxu hxK => ?_
    have hx1 : τ x w1 = w1 := (memfix _ _).1 hw1 x hxK
    have e2 : D * x * D⁻¹ * D = D * x := by group
    have e3 : τ (D * x * D⁻¹) (τ D w1) = τ D w1 := by
      rw [← Module.End.mul_apply, ← map_mul, e2, map_mul, Module.End.mul_apply, hx1]
    have e : l (τ D w1) = chr ψ t (D * x * D⁻¹) * l (τ D w1) := by
      rw [← hequiv _ (conj_up d hxu), e3]
    exact mul_right_cancel₀ hL (e.symm.trans (one_mul _).symm)
  let M : ℕ := ∑ i, (ord k (d i)).natAbs
  have hMi : ∀ i, -(M : ℤ) ≤ ord k (d i) ∧ ord k (d i) ≤ M := by
    intro i
    have h1 : (ord k (d i)).natAbs ≤ M :=
      Finset.single_le_sum (f := fun i => (ord k (d i)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : |ord k (d i)| ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    exact abs_le.1 h2
  have hc : ∀ i j : Fin n, 1 ≤ ((2 * M + 1 : ℕ) : ℤ) + ord k (d j) - ord k (d i) := by
    intro i j
    have a1 := hMi i
    have a2 := hMi j
    push_cast
    linarith [a1.1, a1.2, a2.1, a2.2]
  let Bg : Subgroup (GL (Fin n) k) := (Kc k n 1).comap (MulAut.conj D⁻¹).toMonoidHom
  have hDinv : D⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ d).symm
  have hBmem : ∀ g, g ∈ Bg ↔ D⁻¹ * g * D⁻¹⁻¹ ∈ Kc k n 1 := fun g => Iff.rfl
  have hle : Kc k n (2 * M + 1) ≤ Bg := by
    intro g hg
    rw [hBmem, mem_Kc]
    obtain ⟨hg1, hg2⟩ := mem_Kc.1 hg
    rw [hDinv]
    refine ⟨isoNe_lemma_2 d _ hc hg1, ?_⟩
    have e : (diagT k (Fin n) d⁻¹ * g * (diagT k (Fin n) d⁻¹)⁻¹)⁻¹ =
        diagT k (Fin n) d⁻¹ * g⁻¹ * (diagT k (Fin n) d⁻¹)⁻¹ := by group
    rw [e]
    exact isoNe_lemma_2 d _ hc hg2
  have hfin1 : Bg.relIndex (Kc k n 1) ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Kc_index (2 * M + 1) (Kc_le 1)) (Subgroup.relIndex_dvd_of_le_left _ hle)
  have hw2 : ∀ b ∈ Bg, τ b (τ D w1) = τ D w1 := by
    intro b hb
    have hb' : D⁻¹ * b * D⁻¹⁻¹ ∈ Kc k n 1 := (hBmem b).1 hb
    have e : b * D = D * (D⁻¹ * b * D⁻¹⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hb']
  have hl1 : ∀ a ∈ Kc k n 1, l (τ a (τ D w1)) = (fun _ => (1 : ℂ)) a * l (τ D w1) := by
    intro a ha
    obtain ⟨x, hxu, hxK, s, hsK, y, hy, rfl⟩ := iwahori ha
    have hyc : D⁻¹ * y * D⁻¹⁻¹ ∈ Kc k n 1 := by
      rw [hDinv]
      have hN := conj_Nm (t := d⁻¹) (a := fun i => -ord k (d i)) ?_ (c := 0) (c' := 0) ?_ hy
      · exact (Subgroup.mem_inf.1 hN).2
      · intro i
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, val_ord', _root_.zpow_neg]
      · intro i j hji
        have h' : ord k (d i) ≤ ord k (d j) := hdom hji.le
        push_cast
        linarith
    have hy' : τ y (τ D w1) = τ D w1 := hw2 y ((hBmem y).2 hyc)
    have hsD : diagT k (Fin n) s * D = D * diagT k (Fin n) s := by
      rw [← map_mul, ← map_mul, mul_comm]
    have hs' : τ (diagT k (Fin n) s) (τ D w1) = τ D w1 := by
      rw [← Module.End.mul_apply, ← map_mul, hsD, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hsK]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy', hs', hequiv x hxu,
      chr_one hψ1 ht hxK]
  obtain ⟨w3, -, hw3, hlw3⟩ := avg τ (Kc k n 1) Bg hfin1 (fun _ => (1 : ℂ)) (by simp) (by simp) (by simp)
    (τ D w1) hw2 l hl1 ⊤ (by simp)
  have hw3fix : w3 ∈ fixd τ (Kc k n 1) := (memfix _ _).2 fun g hg => by
    rw [hw3 g hg]
    simp
  obtain ⟨w', hw'P, hw'eig, hlw'⟩ := avg τ (unipB k (Fin n) ⊓ KO k (Fin n)) (Kc k n 1)
    (Kc_index 1 inf_le_right) (chr ψ t)
    (fun a ha b hb => isoNe_lemma ψ t (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)
    (fun a _ => by unfold chr; simp)
    (fun b _ hb => chr_one hψ1 ht hb) w3 (fun b hb => (memfix _ _).1 hw3fix b hb) l
    (fun a ha => hequiv a (Subgroup.mem_inf.1 ha).1 w3) (fixd τ (Kc k n 1))
    (fun a ha => hconj a (Subgroup.mem_inf.1 ha).2 w3 hw3fix)
  rw [Submodule.ne_bot_iff]
  refine ⟨w', ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨hw'P, ?_⟩
    simp only [Submodule.mem_iInf]
    rintro v ⟨hvu, hvK⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hw'eig v (Subgroup.mem_inf.2 ⟨hvu, hvK⟩)
  · intro h0
    rw [h0, map_zero, hlw3] at hlw'
    have hi2 := Kc_index (n := n) (k := k) 1 (H := unipB k (Fin n) ⊓ KO k (Fin n)) inf_le_right
    exact hL (by simpa [hfin1, hi2] using hlw'.symm)

end UpperTheory.V.Z.Desc.V0
