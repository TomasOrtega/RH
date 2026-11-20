import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenSESStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgFiltSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Trivial

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] in

/- English proof (translation)
Establish `h0 : ∀ x : LocalizedModule T M, x = 0`. Introduce `x`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h y s`. Rewrite using `[← LocalizedModule.zero_mk s]`.

Use `LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.smul_def, smul_zero]`. Rewrite using `[smul_comm, hk, smul_zero]`. Conclude with `⟨fun a b => by rw [h0 a, h0 b]⟩`.
-/
theorem loc_subsingleton_of_kill {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by
  have h0 : ∀ x : LocalizedModule T M, x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h y s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm, hk, smul_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

/- English proof (translation)
Establish `: Subsingleton (KH.CechC S ι M 1)` using `⟨fun f g => funext fun I => (h 1 I).elim _ _⟩`. Use `⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[Subsingleton.elim x y]`.

Use `⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0, fun j => j.elim0, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul, Fin.sum_univ_zero]`. Conclude with `(h 0 I).elim _ _`.
-/
theorem h1_vanish_generated_of_localized_subsingleton
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (h 1 I).elim _ _⟩
  refine ⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  · refine ⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0,
      fun j => j.elim0, ?_⟩
    rw [one_smul, Fin.sum_univ_zero]
    exact (h 0 I).elim _ _

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

/- English proof (translation)
Use `⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun _ => disjoint_bot_left) (Subsingleton.elim _ _), fun _ _ _ _ _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)⟩` and prove the remaining obligations.
-/
theorem isMGraded_punit : KH.IsMGraded S ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) := by
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun _ => disjoint_bot_left)
    (Subsingleton.elim _ _), fun _ _ _ _ _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)⟩

end Trivial

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e`. Take `⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩` from `hPF S K ι M 𝓜 hS hfin hgr`. Set `G : ℕ → Set M` to `fun j => m '' {l | (l : ℕ) < j}`. Set `F : ℕ → Submodule (MRingOver S ι) M` to `fun j => Submodule.span _ (G j)`. Establish `hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c'`.

Introduce and unpack `j _ ⟨l, -, rfl⟩`. Conclude with `⟨c l, hm l⟩`. Establish `hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j` using `fun hij => Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)`. Establish `hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j))` using `fun j => (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1`. Establish `key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n → Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧ GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`. Establish `hF0 : F 0 = ⊥` using `by simp [F, G]`.

Use `⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Establish `hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M)`. Rewrite using `[← hF0]`. Conclude with `y.2`.

Conclude with `Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)`. Consider the case `succ j ih`. Introduce `hj`. Take `⟨c₀, hc₀⟩` from `ih (Nat.le_of_succ_le hj)`. Set `l : Fin r` to `⟨j, hj⟩`.

Set `L : Submodule (MRingOver S ι) (F (j + 1))` to `(F j).comap (F (j + 1)).subtype`. Establish `hq` using `(hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2`. Establish `hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l` using `fun p => hcol l p`. Establish `hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j`. Introduce `p hp y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l', hl', rfl⟩` from `hx`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h` into its components or cases. Conclude with `(F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)`.

Rewrite using `[show l' = l from Fin.ext h]`. Conclude with `(hcolj p).2 hp`. Consider the case `zero => rw [smul_zero]`. Conclude with `(F j).zero_mem`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `(F j).add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `(F j).smul_mem a hx`. Establish `hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L)`. Introduce `p hp`.

Rewrite using `[Module.mem_annihilator]`. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective L q`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `show ((p • y : F (j + 1)) : M) ∈ F j`.

Rewrite using `[Submodule.coe_smul]`. Conclude with `hkill p hp y y.2`. Establish `hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L)`. Establish `: Module.Finite (MRingOver S ι) (F (j + 1))` using `Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))`. Use `infer_instance`.

Choose the witnesses or unpack the hypotheses as in `⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n → Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧ GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by`. Distinguish the cases in `hrel : IsMultiProjPrime (𝔭 l)`. Conclude with `hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e`. Establish `hirr : ¬ IsRelevant (𝔭 l)` using `fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩`. Simplify using `only [IsRelevant, not_forall, not_exists, not_not] at hirr`.

Take `⟨k, hk⟩` from `hirr`. Use `⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1 k`. Conclude with `loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩) (Module.mem_annihilator.1 (hann (hk i)))`. Use `⟨max c₀ c₂, fun n hn => ?_⟩` and prove the remaining obligations.

Establish `h0` using `hc₀ n (le_of_max_le_left hn)`. Establish `h2` using `hc₂ n (le_of_max_le_right hn)`. Set `g` to `Submodule.inclusion (hFmono (Nat.le_succ j))`. Establish `hex : LinearMap.range g = LinearMap.ker L.mkQ`. Rewrite using `[Submodule.range_inclusion, Submodule.ker_mkQ]`.

Establish `hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g` using `fun _ _ hx => hx`. Establish `hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L) L.mkQ` using `fun _ _ hx => Submodule.mem_map_of_mem hx`. Establish `H` using `hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1`. Conclude with `⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩`. Establish `hFr : F r = ⊤`.

Rewrite using `[← hspan]`. Simplify using `[F, G]`. Take `⟨c₁, hc₁⟩` from `key r le_rfl`. Use `⟨c₁, fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨h1, hgen⟩` from `hc₁ n hn`.

Set `g` to `(F r).subtype`. Establish `hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit)`. Rewrite using `[Submodule.range_subtype, hFr, LinearMap.ker_zero]`. Establish `hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g` using `fun _ _ hx => hx`. Establish `hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0` using `fun _ _ _ => Submodule.zero_mem _`.

Establish `hU` using `h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι) (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _) (fun _ => ⊥) (e + n • N)`. Establish `H` using `hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1`. Conclude with `⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩`.
-/
theorem H1GenerationDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) (hGS : GenSESStep.Statement) : H1GenerationDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧
        GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l := fun p => hcol l p
      have hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j := by
        intro p hp y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact (F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)
          · rw [show l' = l from Fin.ext h]
            exact (hcolj p).2 hp
        | zero => rw [smul_zero]; exact (F j).zero_mem
        | add x y _ _ hx hy => rw [smul_add]; exact (F j).add_mem hx hy
        | smul a x _ hx => rw [smul_comm]; exact (F j).smul_mem a hx
      have hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L) := by
        intro p hp
        rw [Module.mem_annihilator]
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        show ((p • y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_smul]
        exact hkill p hp y y.2
      have hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L) := by
        have : Module.Finite (MRingOver S ι) (F (j + 1)) :=
          Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))
        infer_instance
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧
            GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        · exact hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e
        · have hirr : ¬ IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          exact loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩)
            (Module.mem_annihilator.1 (hann (hk i)))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      have h0 := hc₀ n (le_of_max_le_left hn)
      have h2 := hc₂ n (le_of_max_le_right hn)
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      have H := hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1
      exact ⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  refine ⟨c₁, fun n hn => ?_⟩
  obtain ⟨h1, hgen⟩ := hc₁ n hn
  let g := (F r).subtype
  have hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit) := by
    rw [Submodule.range_subtype, hFr, LinearMap.ker_zero]
  have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g := fun _ _ hx => hx
  have hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hU := h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι)
    (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _)
    (fun _ => ⊥) (e + n • N)
  have H := hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1
  exact ⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
