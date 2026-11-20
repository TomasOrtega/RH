import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTwistSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

/- English proof (translation)
Use `revert x`. Use `LocalizedModule.induction_on ?_` and prove the remaining obligations. Introduce `m s`. Rewrite using `[locRes_mk, locRes_mk, locRes_mk]`.
-/
theorem locRes_locRes {I J K : Finset (Fin (N + 1))} (h1 : I ⊆ J) (h2 : J ⊆ K) (x : LocMod S N M I) :
    locRes h2 (locRes h1 x) = locRes (h1.trans h2) x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk, locRes_mk, locRes_mk]

/- English proof (translation)
Use `revert x`. Use `LocalizedModule.induction_on ?_` and prove the remaining obligations. Introduce `m s`. Rewrite using `[locRes_mk]`.
-/
theorem locRes_self {I : Finset (Fin (N + 1))} (h : I ⊆ I) (x : LocMod S N M I) : locRes h x = x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk]

/- English proof (translation)
Establish `key : degLoc 𝓜 c I ≤ (degLoc 𝓜 c J).comap (locResS I J h)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hm, hs, hae, rfl⟩`. Use `show locRes h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) ∈ degLoc 𝓜 c J`. Rewrite using `[locRes_mk]`.

Conclude with `Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, rfl⟩`. Conclude with `key hx`.
-/
theorem locRes_mem_degLoc (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    {x : LocMod S N M I.1} (hx : x ∈ degLoc 𝓜 c I) : locRes h x ∈ degLoc 𝓜 c J := by
  have key : degLoc 𝓜 c I ≤ (degLoc 𝓜 c J).comap (locResS I J h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    show locRes h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) ∈ degLoc 𝓜 c J
    rw [locRes_mk]
    exact Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, rfl⟩
  exact key hx

end Loc

section Proof

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

def primeQuotGraded : GradedPMod S N (Poly S N ⧸ primeOf (S := S) y) :=
  quotGraded (primeOf (S := S) y) fun _ hf d => homogeneousComponent_mem_primeOf y hf d

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.span S _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, e, hf, he, rfl⟩`. Simplify using `only [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]`. Introduce `I`.

Conclude with `Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he], by simp⟩`.
-/
theorem coordGraded_piece_le_secs (n : ℕ) :
    (coordGraded S y).piece (n : ℤ) ≤ (twistSys S y (n : ℤ)).secs := by
  change Submodule.span S _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨f, e, hf, he, rfl⟩
  simp only [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

/- English proof (translation)
Rewrite `hz` using `[twistMod_eq_span (n : ℤ) (singleChart hj) (Finset.mem_singleton_self j), Submodule.mem_span_singleton]`. Take `⟨b, rfl⟩` from `hz`. Take `⟨f, s, e, hs, hf, hse, hb⟩` from `b.2`. Establish `hs0 : aeval y s ≠ 0` using `eval_ne_zero_of_mem_monos (singleChart hj) hs`. Use `⟨f * X j ^ n, s, e, hs, hse, hf.mul (isHomogeneous_X_pow j n), ?_⟩` and prove the remaining obligations.

Rewrite using `[chartRing_smul_def, hb, map_mul, map_pow, aeval_X, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_rep_of_mem_twistMod (n : ℕ) {j : Fin (N + 1)} (hj : y j ≠ 0) {z : Ω}
    (hz : z ∈ twistMod S y (n : ℤ) (singleChart hj)) :
    ∃ (g s : Poly S N) (e : ℕ), s ∈ monos ({j} : Finset (Fin (N + 1))) ∧ s.IsHomogeneous e ∧
      g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s := by
  rw [twistMod_eq_span (n : ℤ) (singleChart hj) (Finset.mem_singleton_self j),
    Submodule.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  refine ⟨f * X j ^ n, s, e, hs, hse, hf.mul (isHomogeneous_X_pow j n), ?_⟩
  rw [chartRing_smul_def, hb, map_mul, map_pow, aeval_X, zpow_natCast]
  field_simp

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (q * f) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right f _ hq`.
-/
theorem smul_quot_eq_zero {q : Poly S N} (hq : q ∈ primeOf (S := S) y)
    (m : Poly S N ⧸ primeOf (S := S) y) : q • m = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk _ (q * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right f _ hq

/- English proof (translation)
Use `revert x`. Use `LocalizedModule.induction_on ?_` and prove the remaining obligations. Introduce `m s`. Use `show (LocalizedModule.mk m s : LocalizedModule (monos (S := S) J) _) = 0`. Rewrite using `[← LocalizedModule.zero_mk s]`.

Use `LocalizedModule.mk_eq.mpr ⟨⟨X i, X_mem_monos hi⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_zero, smul_zero, Submonoid.smul_def]`. Conclude with `smul_quot_eq_zero y ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi])) _`.
-/
theorem locMod_quot_eq_zero {J : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ J) (hyi : y i = 0)
    (x : LocMod S N (Poly S N ⧸ primeOf (S := S) y) J) : x = 0 := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  show (LocalizedModule.mk m s : LocalizedModule (monos (S := S) J) _) = 0
  rw [← LocalizedModule.zero_mk s]
  refine LocalizedModule.mk_eq.mpr ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
  rw [smul_zero, smul_zero, Submonoid.smul_def]
  exact smul_quot_eq_zero y
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi])) _

/- English proof (translation)
Rewrite using `[locRes_mk, locRes_mk]`. Use `LocalizedModule.mk_eq.mpr ⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (sb * ga) = Ideal.Quotient.mk _ (sa * gb)`. Rewrite using `[Ideal.Quotient.eq]`.

Establish `h1 : (sb * ga).IsHomogeneous (eb + (ea + n))` using `hsbe.mul hga`. Establish `h2 : (sa * gb).IsHomogeneous (eb + (ea + n))`. Use `hsae.mul hgb` as an intermediate fact. Rewrite `this` using `[show ea + (eb + n) = eb + (ea + n) by omega]`. Then use the resulting hypothesis. Rewrite using `[mem_primeOf_of_isHomogeneous y (h1.sub h2), map_sub, map_mul, map_mul, hza, hzb]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locRes_rep_eq {n : ℕ} {z : Ω} {J : Finset (Fin (N + 1))} {a b : Fin (N + 1)}
    (ha : a ∈ J) (hb : b ∈ J) (ga sa gb sb : Poly S N) (ea eb : ℕ)
    (hsa : sa ∈ monos ({a} : Finset (Fin (N + 1)))) (hsb : sb ∈ monos ({b} : Finset (Fin (N + 1))))
    (hsae : sa.IsHomogeneous ea) (hsbe : sb.IsHomogeneous eb)
    (hga : ga.IsHomogeneous (ea + n)) (hgb : gb.IsHomogeneous (eb + n))
    (hza : aeval y ga = z * aeval y sa) (hzb : aeval y gb = z * aeval y sb) :
    locRes (Finset.singleton_subset_iff.mpr ha)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) ga) ⟨sa, hsa⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {a}) =
      locRes (Finset.singleton_subset_iff.mpr hb)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) gb) ⟨sb, hsb⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {b}) := by
  rw [locRes_mk, locRes_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def]
  change Ideal.Quotient.mk _ (sb * ga) = Ideal.Quotient.mk _ (sa * gb)
  rw [Ideal.Quotient.eq]
  have h1 : (sb * ga).IsHomogeneous (eb + (ea + n)) := hsbe.mul hga
  have h2 : (sa * gb).IsHomogeneous (eb + (ea + n)) := by
    have := hsae.mul hgb
    rwa [show ea + (eb + n) = eb + (ea + n) by omega] at this
  rw [mem_primeOf_of_isHomogeneous y (h1.sub h2), map_sub, map_mul, map_mul, hza, hzb]
  ring

/- English proof (translation)
Introduce `z hz`. Establish `hloc : ∀ j : Fin (N + 1), ∃ w : LocMod S N (Poly S N ⧸ primeOf (S` using `S) y) {j}, w ∈ degLoc (primeQuotGraded (S := S) y) (n : ℤ) ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ ∧ ∀ _ : y j ≠ 0, ∃ (g s : Poly S N) (e : ℕ) (hs : s ∈ monos ({j} : Finset (Fin (N + 1)))), s.IsHomogeneous e ∧ g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s ∧ …`. Introduce `j`. Distinguish the cases in `hj : y j = 0`. Conclude with `⟨0, Submodule.zero_mem _, fun h => absurd hj h⟩`.

Establish `hzj : z ∈ twistMod S y (n : ℤ) (singleChart hj)`. Establish `h'` using `hz`. Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at h'`. Conclude with `h' (singleChart hj)`. Take `⟨g, s, e, hs, hse, hg, hgz⟩` from `exists_rep_of_mem_twistMod y n hj hzj`.

Use `⟨LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩, Submodule.subset_span ⟨Ideal.Quotient.mk (primeOf (S := S) y) g, ⟨s, hs⟩, ((e + n : ℕ) : ℤ), e, mem_quotGraded_piece.mpr ⟨g, isWeightedHomogeneous_int_of_isHomogeneous hg, rfl⟩, hse, by push_cast; ring, rfl⟩, …` and prove the remaining obligations. Use `choose w hwdeg hwrep using hloc`. Establish `hcompat : ∀ (J : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (ha : a ∈ J) (hb : b ∈ J), locRes (Finset.singleton_subset_iff.mpr ha) (w a) = locRes (Finset.singleton_subset_iff.mpr hb) (w b)`. Introduce `J a b ha hb`. Distinguish the cases in `h0 : ∃ i ∈ J, y i = 0`.

Take `⟨i, hi, hyi⟩` from `h0`. Rewrite using `[locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr ha) (w a)), locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr hb) (w b))]`. Use `push Not at h0`. Take `⟨ga, sa, ea, hsa, hsae, hga, hza, hwa⟩` from `hwrep a (h0 a ha)`. Take `⟨gb, sb, eb, hsb, hsbe, hgb, hzb, hwb⟩` from `hwrep b (h0 b hb)`.

Rewrite using `[hwa, hwb]`. Conclude with `locRes_rep_eq y ha hb ga sa gb sb ea eb hsa hsb hsae hsbe hga hgb hza hzb`. Set `v : ∀ I : StdCell N, LocMod S N (Poly S N ⧸ primeOf (S` to `S) y) I.1 := fun I => locRes (Finset.singleton_subset_iff.mpr (I.1.min'_mem I.2.1)) (w (I.1.min' I.2.1))`. Establish `hv : ∀ (I : StdCell N) (a : Fin (N + 1)) (ha : a ∈ I.1), v I = locRes (Finset.singleton_subset_iff.mpr ha) (w a)` using `fun I a ha => hcompat I.1 _ a (I.1.min'_mem I.2.1) ha`. Establish `hvres : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J`.

Introduce `I J h`. Express the relevant statement in the definitionally equal form `locRes h (v I) = v J`. Take `⟨a, ha⟩` from `I.2.1`. Rewrite using `[hv I a ha, hv J a (h ha), locRes_locRes]`. Set `ζ : Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S` to `S) y)) 0 := fun I => v I.1`.

Establish `hζ : ζ ∈ Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S` using `S) y)) (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0 := by`. Use `Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (Cech.d_zero_of_compat (G := locSys S N (Poly S N ⧸ primeOf (S := S) y)) (ρ := locResS) v hvres), ?_⟩` and prove the remaining obligations. Rewrite using `[Cech.Cdeg, Submodule.mem_pi]`. Introduce `I _`. Take `⟨a, ha⟩` from `I.1.2.1`.

Express the relevant statement in the definitionally equal form `v I.1 ∈ _`. Rewrite using `[hv I.1 a ha]`. Conclude with `locRes_mem_degLoc _ _ ⟨{a}, Finset.singleton_nonempty a, Finset.subset_univ _⟩ I.1 _ (hwdeg a)`. Take `⟨m, hm⟩` from `hsurj (Submodule.Quotient.mk ⟨ζ, hζ⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, y j ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hy (funext h)`. Establish `heq : constCochain (m : Poly S N ⧸ primeOf (S` using `S) y) = ζ := by`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (⟨constCochain (m : Poly S N ⧸ primeOf (S := S) y), constCochain_mem _ _ _ m.2⟩ : Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y)) (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0) = _ at hm`.

Establish `h2` using `(Submodule.Quotient.eq _).mp hm`. Rewrite `h2` using `[Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `_ ∈ (⊥ : Submodule S (Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0)) at h2`. Rewrite `h2` using `[Submodule.mem_bot, map_sub]`. Conclude with `sub_eq_zero.mp h2`.

Establish `hj1` using `congrFun heq ⟨⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩, Finset.card_singleton j⟩`. Establish `hvj : v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ = w j`. Rewrite using `[hv _ j (Finset.mem_singleton_self j), locRes_self]`. Take `⟨g, s, e, hs, hse, hg, hgz, hwj⟩` from `hwrep j hj`. Take `⟨f, hf, hfm⟩` from `mem_quotGraded_piece.mp m.2`.

Express the relevant statement in the definitionally equal form `LocalizedModule.mk (m : Poly S N ⧸ primeOf (S := S) y) 1 = v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ at hj1`. Rewrite `hj1` using `[hvj, hwj, ← hfm]`. Take `⟨u, hu⟩` from `LocalizedModule.mk_eq.mp hj1`. Rewrite `hu` using `[one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ ((u : Poly S N) * (s * f)) = Ideal.Quotient.mk _ ((u : Poly S N) * g) at hu`.

Rewrite `hu` using `[Ideal.Quotient.eq, ← mul_sub]`. Establish `hu0 : (u : Poly S N) ∉ primeOf (S` using `S) y := by`. Take `⟨eu, heu⟩` from `monos_isHomogeneous u.2`. Rewrite using `[mem_primeOf_of_isHomogeneous y heu]`. Conclude with `eval_ne_zero_of_mem_monos (singleChart hj) u.2`.

Establish `hsf` using `(Ideal.IsPrime.mem_or_mem inferInstance hu).resolve_left hu0`. Establish `hfh : f.IsHomogeneous n` using `isHomogeneous_of_isWeightedHomogeneous_one hf`. Establish `h1 : (s * f - g).IsHomogeneous (e + n)` using `(hse.mul hfh).sub hg`. Rewrite `hsf` using `[mem_primeOf_of_isHomogeneous y h1, map_sub, map_mul, hgz]`. Establish `hs0 : aeval y s ≠ 0` using `eval_ne_zero_of_mem_monos (singleChart hj) hs`.

Establish `hzf : z = aeval y f`. Establish `h3 : aeval y s * (aeval y f - z) = 0` using `by linear_combination hsf`. Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `absurd h hs0`. Conclude with `(sub_eq_zero.mp h).symm`.

Rewrite using `[hzf]`. Conclude with `Submodule.subset_span ⟨f, n, hfh, rfl, rfl⟩`.
-/
theorem secs_le_of_surjective (hy : y ≠ 0) (n : ℕ)
    (hsurj : Function.Surjective (toH0 (primeQuotGraded (S := S) y) (n : ℤ))) :
    (twistSys S y (n : ℤ)).secs ≤ (coordGraded S y).piece (n : ℤ) := by
  intro z hz
  have hloc : ∀ j : Fin (N + 1), ∃ w : LocMod S N (Poly S N ⧸ primeOf (S := S) y) {j},
      w ∈ degLoc (primeQuotGraded (S := S) y) (n : ℤ)
        ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ ∧
      ∀ _ : y j ≠ 0, ∃ (g s : Poly S N) (e : ℕ) (hs : s ∈ monos ({j} : Finset (Fin (N + 1)))),
        s.IsHomogeneous e ∧ g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s ∧
        w = LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩ := by
    intro j
    by_cases hj : y j = 0
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd hj h⟩
    · have hzj : z ∈ twistMod S y (n : ℤ) (singleChart hj) := by
        have h' := hz
        simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at h'
        exact h' (singleChart hj)
      obtain ⟨g, s, e, hs, hse, hg, hgz⟩ := exists_rep_of_mem_twistMod y n hj hzj
      refine ⟨LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩,
        Submodule.subset_span ⟨Ideal.Quotient.mk (primeOf (S := S) y) g, ⟨s, hs⟩, ((e + n : ℕ) : ℤ), e,
          mem_quotGraded_piece.mpr ⟨g, isWeightedHomogeneous_int_of_isHomogeneous hg, rfl⟩, hse,
          by push_cast; ring, rfl⟩,
        fun _ => ⟨g, s, e, hs, hse, hg, hgz, rfl⟩⟩
  choose w hwdeg hwrep using hloc
  have hcompat : ∀ (J : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (ha : a ∈ J) (hb : b ∈ J),
      locRes (Finset.singleton_subset_iff.mpr ha) (w a) =
        locRes (Finset.singleton_subset_iff.mpr hb) (w b) := by
    intro J a b ha hb
    by_cases h0 : ∃ i ∈ J, y i = 0
    · obtain ⟨i, hi, hyi⟩ := h0
      rw [locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr ha) (w a)),
        locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr hb) (w b))]
    · push Not at h0
      obtain ⟨ga, sa, ea, hsa, hsae, hga, hza, hwa⟩ := hwrep a (h0 a ha)
      obtain ⟨gb, sb, eb, hsb, hsbe, hgb, hzb, hwb⟩ := hwrep b (h0 b hb)
      rw [hwa, hwb]
      exact locRes_rep_eq y ha hb ga sa gb sb ea eb hsa hsb hsae hsbe hga hgb hza hzb
  let v : ∀ I : StdCell N, LocMod S N (Poly S N ⧸ primeOf (S := S) y) I.1 := fun I =>
    locRes (Finset.singleton_subset_iff.mpr (I.1.min'_mem I.2.1)) (w (I.1.min' I.2.1))
  have hv : ∀ (I : StdCell N) (a : Fin (N + 1)) (ha : a ∈ I.1),
      v I = locRes (Finset.singleton_subset_iff.mpr ha) (w a) :=
    fun I a ha => hcompat I.1 _ a (I.1.min'_mem I.2.1) ha
  have hvres : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    change locRes h (v I) = v J
    obtain ⟨a, ha⟩ := I.2.1
    rw [hv I a ha, hv J a (h ha), locRes_locRes]
  let ζ : Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0 := fun I => v I.1
  have hζ : ζ ∈ Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
      (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0 := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr
      (Cech.d_zero_of_compat (G := locSys S N (Poly S N ⧸ primeOf (S := S) y)) (ρ := locResS) v hvres), ?_⟩
    rw [Cech.Cdeg, Submodule.mem_pi]
    intro I _
    obtain ⟨a, ha⟩ := I.1.2.1
    change v I.1 ∈ _
    rw [hv I.1 a ha]
    exact locRes_mem_degLoc _ _ ⟨{a}, Finset.singleton_nonempty a, Finset.subset_univ _⟩ I.1 _ (hwdeg a)
  obtain ⟨m, hm⟩ := hsurj (Submodule.Quotient.mk ⟨ζ, hζ⟩)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have heq : constCochain (m : Poly S N ⧸ primeOf (S := S) y) = ζ := by
    change Submodule.Quotient.mk (⟨constCochain (m : Poly S N ⧸ primeOf (S := S) y),
      constCochain_mem _ _ _ m.2⟩ : Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
        (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0) = _ at hm
    have h2 := (Submodule.Quotient.eq _).mp hm
    rw [Submodule.mem_comap] at h2
    change _ ∈ (⊥ : Submodule S (Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0)) at h2
    rw [Submodule.mem_bot, map_sub] at h2
    exact sub_eq_zero.mp h2
  have hj1 := congrFun heq ⟨⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩,
    Finset.card_singleton j⟩
  have hvj : v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ = w j := by
    rw [hv _ j (Finset.mem_singleton_self j), locRes_self]
  obtain ⟨g, s, e, hs, hse, hg, hgz, hwj⟩ := hwrep j hj
  obtain ⟨f, hf, hfm⟩ := mem_quotGraded_piece.mp m.2
  change LocalizedModule.mk (m : Poly S N ⧸ primeOf (S := S) y) 1 =
    v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ at hj1
  rw [hvj, hwj, ← hfm] at hj1
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hj1
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def] at hu
  change Ideal.Quotient.mk _ ((u : Poly S N) * (s * f)) = Ideal.Quotient.mk _ ((u : Poly S N) * g) at hu
  rw [Ideal.Quotient.eq, ← mul_sub] at hu
  have hu0 : (u : Poly S N) ∉ primeOf (S := S) y := by
    obtain ⟨eu, heu⟩ := monos_isHomogeneous u.2
    rw [mem_primeOf_of_isHomogeneous y heu]
    exact eval_ne_zero_of_mem_monos (singleChart hj) u.2
  have hsf := (Ideal.IsPrime.mem_or_mem inferInstance hu).resolve_left hu0
  have hfh : f.IsHomogeneous n := isHomogeneous_of_isWeightedHomogeneous_one hf
  have h1 : (s * f - g).IsHomogeneous (e + n) := (hse.mul hfh).sub hg
  rw [mem_primeOf_of_isHomogeneous y h1, map_sub, map_mul, hgz] at hsf
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have hzf : z = aeval y f := by
    have h3 : aeval y s * (aeval y f - z) = 0 := by linear_combination hsf
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hs0
    · exact (sub_eq_zero.mp h).symm
  rw [hzf]
  exact Submodule.subset_span ⟨f, n, hfh, rfl, rfl⟩

end Proof

/- English proof (translation)
Introduce `S _ _ Ω _ _ N y hy`. Take `⟨c₀, hc₀⟩` from `h S N (Poly S N ⧸ primeOf (S := S) y) (primeQuotGraded y) (finite_quot _)`. Rewrite using `[Filter.eventually_atTop]`. Use `⟨c₀.toNat, fun n hn => le_antisymm ?_ (coordGraded_piece_le_secs y n)⟩` and prove the remaining obligations. Conclude with `secs_le_of_surjective y hy n (hc₀ n ((Int.self_le_toNat c₀).trans (by exact_mod_cast hn)))`.
-/
theorem TwistSections.proof (h : SerreOnto.Statement.{u, u}) : TwistSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N y hy
  obtain ⟨c₀, hc₀⟩ := h S N (Poly S N ⧸ primeOf (S := S) y) (primeQuotGraded y) (finite_quot _)
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun n hn => le_antisymm ?_ (coordGraded_piece_le_secs y n)⟩
  exact secs_le_of_surjective y hy n (hc₀ n ((Int.self_le_toNat c₀).trans (by exact_mod_cast hn)))

end

end GroundTheory.Heights₂.Heights.Kleiman
