import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.SmulEqAlgebraMapMul
import Lemmata.GeneralBFactThirdMore.Key

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af := fun i => Formalism.UG.inclE (F := F) Af (w i)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩`.
-/
theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)`.
-/
theorem one_tmul_mem_intAf {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)`.
-/
theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))`. Use `⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩` and prove the remaining obligations. Establish `key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F → (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F` using `F) L := by`. Introduce `j k c hc`. Take `⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p` from `Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))`.

Establish `hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L`. Rewrite using `[hq, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hmL (j, k)) q`. Establish `heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) = (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) • inclV (F` using `F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']`. Simplify using `only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Simplify using `[Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]`. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ _ (inclV_mem hw)`. Establish `hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af)` using `by conv_lhs => rw [← Finset.univ_sum_single y]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h1` using `emb_coord b (y j)`. Simplify using `only [emb] at h1`. Use `conv_lhs => rw [← h1]`. Conclude with `map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _`. Rewrite using `[hy', Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Conclude with `Submodule.sum_mem _ fun k _ => key j k _ (hy j k)`.
-/
theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L`. Take `⟨p, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`. Take `⟨D, hD, h⟩` from `exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)`. Use `⟨D, hD, fun l hl j k => ?_⟩` and prove the remaining obligations.

Establish `hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; trivial`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem`. Establish `hl' : l = ∑ t, c t • (s t : Fin n → E)`. Use `congrArg Subtype.val hc` as an intermediate fact. Simplify `this.symm` using `[Submodule.coe_sum]`.

Establish `: (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k)`. Rewrite using `[hl']`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Rewrite using `[← b.coord_apply, map_sum]`. Simplify using `only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]`.

Unfold `IntF`. Rewrite using `[this, map_sum]`. Conclude with `ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _`.
-/
theorem exists_den_lattice (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
  classical
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨p, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  obtain ⟨D, hD, h⟩ := exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)
  refine ⟨D, hD, fun l hl j k => ?_⟩
  have hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hl' : l = ∑ t, c t • (s t : Fin n → E) := by
    have := congrArg Subtype.val hc
    simpa [Submodule.coe_sum] using this.symm
  have : (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k) := by
    rw [hl']
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [← b.coord_apply, map_sum]
    simp only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]
  unfold IntF
  rw [this, map_sum]
  exact ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _

end PI.WAU
