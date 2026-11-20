import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRatioOfLocalGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.BdSec

section Alg

open Scheme.IdealSheafData

/- English proof (translation)
Use `((GlobalTheory.VanStalk.van_spec G.support x).2 q).2 ?_` and prove the remaining obligations. Take `⟨W, hxW, -⟩` from `EffCartierData.exists_affine_le (V := ⊤) (x := x) trivial`. Rewrite using `[vanishingIdeal_support, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW]`. Rewrite `h` using `[ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW]`. Conclude with `(Ideal.map_radical_le _).trans (q.isPrime.radical_le_iff.2 h)`.
-/
theorem fromSpecStalk_mem_support {X : Scheme.{0}} (G : X.IdealSheafData) (x : X)
    (q : PrimeSpectrum (X.presheaf.stalk x)) (h : stalkId G x ≤ q.asIdeal) : X.fromSpecStalk x q ∈ G.support := by
  refine ((GlobalTheory.VanStalk.van_spec G.support x).2 q).2 ?_
  obtain ⟨W, hxW, -⟩ := EffCartierData.exists_affine_le (V := ⊤) (x := x) trivial
  rw [vanishingIdeal_support, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW]
  rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW] at h
  exact (Ideal.map_radical_le _).trans (q.isPrime.radical_le_iff.2 h)

/- English proof (translation)
Take `⟨W, hxW, -⟩` from `EffCartierData.exists_affine_le (V := ⊤) (x := x) trivial`. Rewrite using `[ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ y W (h.mem_open W.1.isOpen hxW), Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]`.
-/
theorem stalkId_specializes {X : Scheme.{0}} (G : X.IdealSheafData) {x y : X} (h : y ⤳ x) :
    stalkId G y = (stalkId G x).map (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨W, hxW, -⟩ := EffCartierData.exists_affine_le (V := ⊤) (x := x) trivial
  rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x W hxW,
    ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ y W (h.mem_open W.1.isOpen hxW), Ideal.map_map,
    ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]

/- English proof (translation)
Take `⟨hreg, n, r, e, hr, hst⟩` from `hx`. Use `haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing`. Take `⟨γ, hγ⟩` from `hp`. Express the relevant statement in the definitionally equal form `stalkId G x = Ideal.span {γ} at hγ`. Set `J : Finset (Fin n)` to `Finset.univ.map e`.

Establish `hrad : (∏ j ∈ J, r j) ∈ (Ideal.span {γ}).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `Q ⟨hQγ, hQ⟩`. Take `⟨i, hi⟩` from `hG _ (fromSpecStalk_mem_support G x ⟨Q, hQ⟩ (hγ ▸ hQγ))`. Establish `h1` using `((GlobalTheory.VanStalk.van_spec (C i) x).2 ⟨Q, hQ⟩).1 hi`.

Distinguish the cases in `hxi : x ∈ C i`. Rewrite `h1` using `[hst ⟨i, hxi⟩, Ideal.span_singleton_le_iff_mem]`. Conclude with `Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _))) h1`. Rewrite `h1` using `[GlobalTheory.VanStalk.van_eq_top _ hxi]`. Conclude with `absurd (top_le_iff.1 h1) hQ.ne_top`.

Establish `hγ0 : γ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hrad` using `[Ideal.span_singleton_zero, Ideal.radical_bot_of_noZeroDivisors, Ideal.mem_bot, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj⟩` from `hrad`. Conclude with `(ReciprocityTheory.AnForm.R.prime_of_regular_params r hr.1 hr.2 j).ne_zero hj`.

Take `⟨u, m, -, hm⟩` from `ReciprocityTheory.AnForm.R.eq_unit_mul_monomial r hr.1 hr.2 J hγ0 hrad`. Use `⟨fun i => if h : x ∈ C i then m (e ⟨i, h⟩) else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hγ, hm, Ideal.span_singleton_mul_left_unit u.isUnit, Finset.prod_map, ← Ideal.prod_span_singleton, ← Fintype.prod_subtype_mul_prod_subtype (fun i => x ∈ C i)]`. Rewrite using `[Finset.prod_eq_one (s := Finset.univ) (f := fun i : {i // ¬ x ∈ C i} => _) (fun i _ => by beta_reduce; rw [dif_neg i.2, pow_zero]), mul_one]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[dif_pos i.2, hst i, Ideal.span_singleton_pow]`.
-/
theorem exists_stalkId_eq_prod {X : Scheme.{0}} {q : ℕ} {C : Fin q → Closeds X} (G : X.IdealSheafData)
    (hG : ∀ y ∈ G.support, ∃ i, y ∈ C i) {x : X} (hx : LSncAt X C x) (hp : (stalkId G x).IsPrincipal) :
    ∃ m : Fin q → ℕ, stalkId G x = ∏ i, stalkId (vanishingIdeal (C i)) x ^ m i := by
  classical
  obtain ⟨hreg, n, r, e, hr, hst⟩ := hx
  haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨γ, hγ⟩ := hp
  change stalkId G x = Ideal.span {γ} at hγ
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, r j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    obtain ⟨i, hi⟩ := hG _ (fromSpecStalk_mem_support G x ⟨Q, hQ⟩ (hγ ▸ hQγ))
    have h1 := ((GlobalTheory.VanStalk.van_spec (C i) x).2 ⟨Q, hQ⟩).1 hi
    by_cases hxi : x ∈ C i
    · rw [hst ⟨i, hxi⟩, Ideal.span_singleton_le_iff_mem] at h1
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _))) h1
    · rw [GlobalTheory.VanStalk.van_eq_top _ hxi] at h1
      exact absurd (top_le_iff.1 h1) hQ.ne_top
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.radical_bot_of_noZeroDivisors, Ideal.mem_bot,
      Finset.prod_eq_zero_iff] at hrad
    obtain ⟨j, -, hj⟩ := hrad
    exact (ReciprocityTheory.AnForm.R.prime_of_regular_params r hr.1 hr.2 j).ne_zero hj
  obtain ⟨u, m, -, hm⟩ := ReciprocityTheory.AnForm.R.eq_unit_mul_monomial r hr.1 hr.2 J hγ0 hrad
  refine ⟨fun i => if h : x ∈ C i then m (e ⟨i, h⟩) else 0, ?_⟩
  rw [hγ, hm, Ideal.span_singleton_mul_left_unit u.isUnit, Finset.prod_map, ← Ideal.prod_span_singleton,
    ← Fintype.prod_subtype_mul_prod_subtype (fun i => x ∈ C i)]
  rw [Finset.prod_eq_one (s := Finset.univ) (f := fun i : {i // ¬ x ∈ C i} => _) (fun i _ => by beta_reduce; rw [dif_neg i.2, pow_zero]), mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  beta_reduce
  rw [dif_pos i.2, hst i, Ideal.span_singleton_pow]

/- English proof (translation)
Establish `hG : ∀ y ∈ G.support, ∃ i, y ∈ C i` using `fun y hy => Set.mem_iUnion.1 (hC.2.1.ge hy)`. Use `choose m hm using fun x => exists_stalkId_eq_prod G hG (hx x) (hp x)`. Set `η : Fin q → X` to `fun i => (hC.1 i).genericPoint`. Establish `hη : ∀ i, IsGenericPoint (η i) (C i : Set X)` using `fun i => (hC.1 i).isGenericPoint_genericPoint (C i).isClosed`. Establish `hne : ∀ i j, j ≠ i → η i ∉ C j` using `fun i j hij h => hij (hC.2.2 i j (((hη i).mem_closed_set_iff (C j).isClosed).1 h)).symm`.

Establish `hone : ∀ i (k : Fin q → ℕ), ∏ j, stalkId (vanishingIdeal (C j)) (η i) ^ k j = stalkId (vanishingIdeal (C i)) (η i) ^ k i` using `fun i k => Finset.prod_eq_single i (fun j _ hj => by rw [GlobalTheory.VanStalk.van_eq_top _ (hne i j hj), Ideal.top_pow, Ideal.one_eq_top]) (fun h => absurd (Finset.mem_univ i) h)`. Establish `hinj : ∀ i (a b : ℕ), stalkId (vanishingIdeal (C i)) (η i) ^ a = stalkId (vanishingIdeal (C i)) (η i) ^ b → a = b`. Introduce `i a b h`. Take `⟨hreg, n, r, e, hr, hst⟩` from `hx (η i)`. Use `haveI : IsDomain (X.presheaf.stalk (η i)) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing`.

Establish `hpr` using `ReciprocityTheory.AnForm.R.prime_of_regular_params r hr.1 hr.2 (e ⟨i, (hη i).mem⟩)`. Rewrite `h` using `[hst ⟨i, (hη i).mem⟩, Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]`. Conclude with `le_antisymm ((pow_dvd_pow_iff hpr.ne_zero hpr.not_unit).1 h.dvd) ((pow_dvd_pow_iff hpr.ne_zero hpr.not_unit).1 h.symm.dvd)`. Use `⟨fun i => m (η i) i, fun i => Nat.pos_of_ne_zero fun h0 => ?_, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `hm (η i) beta_reduce at h0`.

Rewrite `h1` using `[hone, h0, pow_zero, Ideal.one_eq_top]`. Conclude with `(ReciprocityTheory.AnForm.R.mem_support_iff_stalkId G (η i)).1 (hC.2.1.le (Set.mem_iUnion.2 ⟨i, (hη i).mem⟩)) h1`. Rewrite using `[hm x]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hxi : x ∈ C i`.

Use `congr 1`. Establish `hs : η i ⤳ x` using `(hη i).specializes hxi`. Use `hinj i _ _ ?_` and prove the remaining obligations. Rewrite using `[← hone i (m x), ← hone i (m (η i)), ← hm (η i), stalkId_specializes G hs, hm x, ← Ideal.mapHom_apply, map_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, Ideal.mapHom_apply, ← stalkId_specializes]`. Rewrite using `[GlobalTheory.VanStalk.van_eq_top _ hxi, Ideal.top_pow, Ideal.top_pow]`.
-/
theorem exists_mult {X : Scheme.{0}} {q : ℕ} {C : Fin q → Closeds X} (G : X.IdealSheafData)
    (hC : CompList (G.support : Set X) C) (hx : ∀ x, LSncAt X C x) (hp : ∀ x, (stalkId G x).IsPrincipal) :
    ∃ mu : Fin q → ℕ, (∀ i, 1 ≤ mu i) ∧ ∀ x, stalkId G x = ∏ i, stalkId (vanishingIdeal (C i)) x ^ mu i := by
  classical
  have hG : ∀ y ∈ G.support, ∃ i, y ∈ C i := fun y hy =>
    Set.mem_iUnion.1 (hC.2.1.ge hy)
  choose m hm using fun x => exists_stalkId_eq_prod G hG (hx x) (hp x)
  let η : Fin q → X := fun i => (hC.1 i).genericPoint
  have hη : ∀ i, IsGenericPoint (η i) (C i : Set X) := fun i => (hC.1 i).isGenericPoint_genericPoint (C i).isClosed
  have hne : ∀ i j, j ≠ i → η i ∉ C j := fun i j hij h =>
    hij (hC.2.2 i j (((hη i).mem_closed_set_iff (C j).isClosed).1 h)).symm
  have hone : ∀ i (k : Fin q → ℕ), ∏ j, stalkId (vanishingIdeal (C j)) (η i) ^ k j =
      stalkId (vanishingIdeal (C i)) (η i) ^ k i := fun i k =>
    Finset.prod_eq_single i (fun j _ hj => by rw [GlobalTheory.VanStalk.van_eq_top _ (hne i j hj), Ideal.top_pow, Ideal.one_eq_top])
      (fun h => absurd (Finset.mem_univ i) h)
  have hinj : ∀ i (a b : ℕ), stalkId (vanishingIdeal (C i)) (η i) ^ a = stalkId (vanishingIdeal (C i)) (η i) ^ b → a = b := by
    intro i a b h
    obtain ⟨hreg, n, r, e, hr, hst⟩ := hx (η i)
    haveI : IsDomain (X.presheaf.stalk (η i)) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    have hpr := ReciprocityTheory.AnForm.R.prime_of_regular_params r hr.1 hr.2 (e ⟨i, (hη i).mem⟩)
    rw [hst ⟨i, (hη i).mem⟩, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_eq_span_singleton] at h
    exact le_antisymm ((pow_dvd_pow_iff hpr.ne_zero hpr.not_unit).1 h.dvd)
      ((pow_dvd_pow_iff hpr.ne_zero hpr.not_unit).1 h.symm.dvd)
  refine ⟨fun i => m (η i) i, fun i => Nat.pos_of_ne_zero fun h0 => ?_, fun x => ?_⟩
  · have h1 := hm (η i)
    beta_reduce at h0
    rw [hone, h0, pow_zero, Ideal.one_eq_top] at h1
    exact (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId G (η i)).1 (hC.2.1.le (Set.mem_iUnion.2 ⟨i, (hη i).mem⟩)) h1
  · rw [hm x]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hxi : x ∈ C i
    · congr 1
      have hs : η i ⤳ x := (hη i).specializes hxi
      refine hinj i _ _ ?_
      rw [← hone i (m x), ← hone i (m (η i)), ← hm (η i), stalkId_specializes G hs, hm x, ← Ideal.mapHom_apply, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [map_pow, Ideal.mapHom_apply, ← stalkId_specializes]
    · rw [GlobalTheory.VanStalk.van_eq_top _ hxi, Ideal.top_pow, Ideal.top_pow]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `stalkId (vanishingIdeal (GlobalTheory.TorRef.pre π (C i))) y = _`. Rewrite using `[GlobalTheory.VanStalk.van_pre]`. Distinguish the cases in `hi : π y ∈ C i`. Take `⟨_, n, r, e, hr, hst⟩` from `h haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)`. Take `⟨g, s, hs⟩` from `GlobalTheory.T.flat_extension_regular_sequence _ _ (π.stalkMap y).hom (Flat.stalkMap π y) (GlobalTheory.T.smooth_fibre_regular_local_ring X Y π y) n r hr`.

Use `haveI : IsRegularLocalRing (Y.presheaf.stalk y) := by`. Use `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_` and prove the remaining obligations. Rewrite using `[← hs.2, ← hs.1]`. Establish `h1` using `Submodule.spanFinrank_span_le_ncard_of_finite (R := Y.presheaf.stalk y) (Set.finite_range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s))`. Establish `h2 : (Set.range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s)).ncard ≤ n + g`.

Rewrite using `[← Set.image_univ]`. Conclude with `(Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])`. Conclude with `h1.trans h2` after adjusting the coercions. Establish `hp` using `ReciprocityTheory.AnForm.R.prime_of_regular_params _ hs.1 hs.2 (Fin.castAdd g (e ⟨i, hi⟩))`. Rewrite `hp` using `[Fin.append_left]`.

Rewrite using `[hst ⟨i, hi⟩, Ideal.map_span, Set.image_singleton]`. Conclude with `((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical`. Rewrite using `[GlobalTheory.VanStalk.van_eq_top _ hi, Ideal.map_top, Ideal.radical_top]`.
-/
theorem stalkId_preimage {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) [Smooth p] (π : Y ⟶ X) [Smooth π] {m : ℕ}
    {C : Fin m → Closeds X} (y : Y) (h : LSncAt X C (π y)) (i : Fin m) :
    stalkId (vanishingIdeal ((C i).preimage π.continuous)) y =
      (stalkId (vanishingIdeal (C i)) (π y)).map (π.stalkMap y).hom := by
  change stalkId (vanishingIdeal (GlobalTheory.TorRef.pre π (C i))) y = _
  rw [GlobalTheory.VanStalk.van_pre]
  by_cases hi : π y ∈ C i
  · obtain ⟨_, n, r, e, hr, hst⟩ := h
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
    obtain ⟨g, s, hs⟩ := GlobalTheory.T.flat_extension_regular_sequence _ _ (π.stalkMap y).hom (Flat.stalkMap π y) (GlobalTheory.T.smooth_fibre_regular_local_ring X Y π y) n r hr
    haveI : IsRegularLocalRing (Y.presheaf.stalk y) := by
      refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
      rw [← hs.2, ← hs.1]
      have h1 := Submodule.spanFinrank_span_le_ncard_of_finite
        (R := Y.presheaf.stalk y) (Set.finite_range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s))
      have h2 : (Set.range (Fin.append (fun i => (π.stalkMap y).hom (r i)) s)).ncard ≤ n + g := by
        rw [← Set.image_univ]
        exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
      exact_mod_cast h1.trans h2
    have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params _ hs.1 hs.2 (Fin.castAdd g (e ⟨i, hi⟩))
    rw [Fin.append_left] at hp
    rw [hst ⟨i, hi⟩, Ideal.map_span, Set.image_singleton]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  · rw [GlobalTheory.VanStalk.van_eq_top _ hi, Ideal.map_top, Ideal.radical_top]

end Alg

section An

open scoped ContDiff

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {m : ℕ} {C : Fin m → Closeds Y.X}
  {n : Fin m → Pts Y σ → ℝ} (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i)) (mu : Fin m → ℕ)

def wPot : LocPot (Pts Y σ) where
  U := (DivSec.divPot hn).U
  isOpen_U := (DivSec.divPot hn).isOpen_U
  mem_U := (DivSec.divPot hn).mem_U
  φ y z := ∑ i, (mu i : ℝ) * (DivSec.eqF hn i y z / 2)

def wSec (y z : Pts Y σ) : ℂ := ∏ i, ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) z ^ mu i

/- English proof (translation)
Establish `h1 : ∀ i, n i z = ‖ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) z‖ * Real.exp (-(DivSec.eqF hn i y z / 2))` using `fun i => by`. Establish `e` using `(DivSec.eq_spec hn i y).2.2.2 z (DivSec.mem_eqV hn hz i)`. Establish `h0` using `((hn i).1 z).1`. Establish `hx : Real.exp (-DivSec.eqF hn i y z) = Real.exp (-(DivSec.eqF hn i y z / 2)) ^ 2`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e` using `[hx, ← mul_pow]`. Conclude with `(pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e`.

Simplify using `only [wSec, wPot, norm_prod, norm_pow, h1, mul_pow, ← Real.exp_nat_mul]`. Rewrite using `[Finset.prod_mul_distrib, ← Real.exp_sum]`. Use `congr 2`. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem norm_wSec_mul {y z : Pts Y σ} (hz : z ∈ (DivSec.divPot hn).U y) :
    ‖wSec hn mu y z‖ * Real.exp (-(wPot hn mu).φ y z) = ∏ i, n i z ^ mu i := by
  have h1 : ∀ i, n i z = ‖ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) z‖ *
      Real.exp (-(DivSec.eqF hn i y z / 2)) := fun i => by
    have e := (DivSec.eq_spec hn i y).2.2.2 z (DivSec.mem_eqV hn hz i)
    have h0 := ((hn i).1 z).1
    have hx : Real.exp (-DivSec.eqF hn i y z) = Real.exp (-(DivSec.eqF hn i y z / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hx, ← mul_pow] at e
    exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [wSec, wPot, norm_prod, norm_pow, h1, mul_pow, ← Real.exp_nat_mul]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Introduce `j` and use `by have h : ∀ i, DifferentiableOn ℂ (fun v => ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) (((Y.an σ).chart j).e.symm v)) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (DivSec.divPot hn).U y) := fun i => ((Y.an σ).holoOn_ev _ (DivSec.eqT hn i y) j).mono fun …`.
-/
theorem holoOn_wSec (y : Pts Y σ) : (Y.an σ).HoloOn ((DivSec.divPot hn).U y) (wSec hn mu y) := fun j => by
  have h : ∀ i, DifferentiableOn ℂ
      (fun v => ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) (((Y.an σ).chart j).e.symm v))
      (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (DivSec.divPot hn).U y) := fun i =>
    ((Y.an σ).holoOn_ev _ (DivSec.eqT hn i y) j).mono fun v hv => ⟨hv.1, DivSec.mem_eqV hn hv.2 i⟩
  have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
      (fun v => ∏ i ∈ s, ev Y.str σ (DivSec.eqV hn i y).1 (DivSec.eqT hn i y) (((Y.an σ).chart j).e.symm v) ^ mu i)
      (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (DivSec.divPot hn).U y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact ((h a).pow (mu a)).mul ih
  refine (key Finset.univ).congr fun v _ => ?_
  simp [wSec]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun y => (hB.holoOn_iff (Y.an σ) ((DivSec.divPot hn).isOpen_U y)).2 (holoOn_wSec hn mu y), fun _ _ _ hz => (norm_wSec_mul hn mu hz.1).trans (norm_wSec_mul hn mu hz.2).symm⟩`.
-/
theorem isSection_wSec {B : FinHolAtlas Y.dim (Pts Y σ)} (hB : IsAlgAtlas B) : IsSection B (wPot hn mu) (wSec hn mu) :=
  ⟨fun y => (hB.holoOn_iff (Y.an σ) ((DivSec.divPot hn).isOpen_U y)).2 (holoOn_wSec hn mu y),
    fun _ _ _ hz => (norm_wSec_mul hn mu hz.1).trans (norm_wSec_mul hn mu hz.2).symm⟩

/- English proof (translation)
Establish `h : ∀ i, (Y.an σ).SmoothOn ((DivSec.divPot hn).U x) (fun z => (mu i : ℝ) * (DivSec.eqF hn i x z / 2))` using `fun i j => contDiffOn_const.mul ((((DivSec.eq_spec hn i x).2.2.1.mono fun z hz => DivSec.mem_eqV hn hz i) j).div_const 2)`. Introduce `j`. Establish `key : ∀ s : Finset (Fin m), ContDiffOn ℝ ∞ ((fun z => ∑ i ∈ s, (mu i : ℝ) * (DivSec.eqF hn i x z / 2)) ∘ ((Y.an σ).chart j).e.symm) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (DivSec.divPot hn).U x)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact (contDiffOn_const (c := (0 : ℝ))).congr fun v _ => by simp`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(h a j).add ih`. Conclude with `key Finset.univ`.
-/
theorem smoothOn_wPot (x : Pts Y σ) : (Y.an σ).SmoothOn ((DivSec.divPot hn).U x) ((wPot hn mu).φ x) := by
  have h : ∀ i, (Y.an σ).SmoothOn ((DivSec.divPot hn).U x) (fun z => (mu i : ℝ) * (DivSec.eqF hn i x z / 2)) := fun i j =>
    contDiffOn_const.mul ((((DivSec.eq_spec hn i x).2.2.1.mono fun z hz => DivSec.mem_eqV hn hz i) j).div_const 2)
  intro j
  have key : ∀ s : Finset (Fin m), ContDiffOn ℝ ∞
      ((fun z => ∑ i ∈ s, (mu i : ℝ) * (DivSec.eqF hn i x z / 2)) ∘ ((Y.an σ).chart j).e.symm)
      (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' (DivSec.divPot hn).U x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact (contDiffOn_const (c := (0 : ℝ))).congr fun v _ => by simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a j).add ih
  exact key Finset.univ

omit [NumberField F] in

/- English proof (translation)
Introduce `hmem`. Take `⟨-, nn, r, emb, hR, -⟩` from `hsnc (genericPoint Y.X)`. Establish `h0 : ringKrullDim (Y.X.presheaf.stalk (genericPoint Y.X)) = 0` using `ringKrullDim_eq_zero_of_field (Y.X.functionField)`. Establish `hn0 : nn = 0`. Use `hR.2` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this` after adjusting the coercions. Substitute `hn0` using the available equality. Conclude with `(emb ⟨i, hmem⟩).elim0`.
-/
theorem generic_notMem (hsnc : ∀ y : Y.X, LSncAt Y.X C y) (i : Fin m) : genericPoint Y.X ∉ C i := by
  intro hmem
  obtain ⟨-, nn, r, emb, hR, -⟩ := hsnc (genericPoint Y.X)
  have h0 : ringKrullDim (Y.X.presheaf.stalk (genericPoint Y.X)) = 0 :=
    ringKrullDim_eq_zero_of_field (Y.X.functionField)
  have hn0 : nn = 0 := by
    have := hR.2
    rw [h0] at this
    exact_mod_cast this
  subst hn0
  exact (emb ⟨i, hmem⟩).elim0

/- English proof (translation)
Introduce `x`. Set `S : Finset (Fin m)` to `Finset.univ.filter fun i => LiesIn x (C i)`. Establish `hS : ∀ i, i ∈ S ↔ LiesIn x (C i)` using `fun i => by simp [S]`. Take `⟨c, hc⟩` from `AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x`. Set `W : Y.X.Opens` to `Finset.univ.inf fun i => (DivSec.eqV hn i x).1`.

Establish `hWle : ∀ i, W ≤ (DivSec.eqV hn i x).1` using `fun i => Finset.inf_le (Finset.mem_univ i)`. Establish `hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (DivSec.eqV hn i x).1) ↔ ∀ i ∈ s, z ∈ ptsIn Y.str σ (DivSec.eqV hn i x).1`. Introduce `z s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]`. Establish `hWU : ptsIn Y.str σ W = (DivSec.divPot hn).U x`. Use extensionality with `z`. Rewrite using `[hmemI z Finset.univ]`. Simplify using `only [DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]`.

Establish `hxW : x ∈ ptsIn Y.str σ W` using `hWU ▸ (DivSec.divPot hn).mem_U x`. Set `ix : Fin S.card → Fin m` to `fun j => (S.equivFin.symm j).1`. Establish `hix : Function.Injective ix` using `fun i j h => S.equivFin.symm.injective (Subtype.ext h)`. Establish `hixS : ∀ j, LiesIn x (C (ix j))` using `fun j => (hS _).1 (S.equivFin.symm j).2`. Set `g : Fin S.card → Γ(Y.X, W)` to `fun j => resG Y.X (hWle (ix j)) (DivSec.eqT hn (ix j) x)`.

Establish `hgev : ∀ i z, z ∈ ptsIn Y.str σ W → ev Y.str σ W (resG Y.X (hWle i) (DivSec.eqT hn i x)) z = ev Y.str σ _ (DivSec.eqT hn i x) z` using `fun i z hz => ev_res _ hz _`. Establish `hzero : ∀ i z, z ∈ ptsIn Y.str σ W → (ev Y.str σ _ (DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i))` using `fun i z hz => ev_eq_zero_iff (DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)`. Establish `h0 : ∀ j, ev Y.str σ W (g j) x = 0` using `fun j => by`. Simplify using `only [g]`. Rewrite using `[hgev _ _ hxW]`.

Conclude with `(hzero _ _ hxW).2 (hixS j)`. Establish `hliA` using `DivSec.linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => DivSec.eqV hn i x) (fun i => DivSec.eqT hn i x) (fun i => (DivSec.eq_spec hn i x).1) (fun i => (DivSec.eq_spec hn i x).2.1)`. Establish `hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x))`. Establish `h2` using `hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i})) (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Establish `e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)] ev Y.str σ _ (DivSec.eqT hn (ix j) x) ∘ c.e.symm` using `Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2`. Simplify using `only [Function.comp_apply]`. Conclude with `e.fderiv_eq`. Establish `hcard : S.card ≤ Y.dim`.

Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self, _root_.mul_one]`. Simplify `this` using `[ReciprocityTheory.L2DbarEstimates.V]`. Take `⟨e, hx0, hsub, -, hhol, hsymm, hev⟩` from `SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli`. Set `O : Set (Pts Y σ)` to `(DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}`.

Establish `hO : IsOpen O`. Use `((DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)` and prove the remaining obligations. Distinguish the cases in `h : LiesIn x (C k)`. Simplify using `[h]`. Simplify `isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)` using `[h]`.

Set `ψ` to `e.restrOpen O hO`. Establish `hψs : ψ.source = e.source ∩ O` using `e.restrOpen_source O hO`. Establish `hψa : ∀ z, ψ z = e z` using `fun z => rfl`. Establish `hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W` using `fun z hz => hsub (hψs ▸ hz).1`. Establish `hψO : ∀ z ∈ ψ.source, z ∈ O` using `fun z hz => (hψs ▸ hz).2`.

Establish `hcompat : IsCompatChart B ψ`. Use `DivSec.isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_` and prove the remaining obligations. Introduce `V _ _ _ B' y hB' hy hm`. Conclude with `hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)`. Conclude with `GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1`.

Set `pos : ∀ k, LiesIn x (C k) → Fin Y.dim` to `fun k hk => ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩`. Set `τ : Fin m → Option (Fin Y.dim)` to `fun k => if hk : LiesIn x (C k) then some (pos k hk) else none`. Establish `hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (DivSec.eqT hn k x) z`. Introduce `k hk z hz`. Rewrite using `[hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]`.

Establish `hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩` using `rfl`. Establish `hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k` using `by simp [ix]`. Rewrite using `[hj]`. Simplify using `only [g]`. Rewrite using `[hgev _ _ (hψW z hz)]`.

Rewrite using `[hk']`. Use `⟨ψ, hcompat, hψs ▸ ⟨hx0, (DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩, fun z hz => (hψO z hz).1, τ, ?_, ?_, fun z => ∏ k ∈ Finset.univ.filter (fun k => ¬ LiesIn x (C k)), ev Y.str σ _ (DivSec.eqT hn k x) z ^ mu k, ?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : LiesIn x (C k)`. Conclude with `Or.inl h`. Conclude with `Or.inr h`.

Introduce `k k' i h1 h2`. Simplify using `only [τ] at h1 h2`. Use `split_ifs at h1 h2 with hk hk'`. Use `(Option.some.inj h1).trans (Option.some.inj h2).symm` as an intermediate fact. Establish `h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩` using `Fin.ext (by simpa [pos] using congrArg Fin.val this)`.

Conclude with `congrArg Subtype.val (S.equivFin.injective h3)`. Introduce `k`. Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hzk, hz⟩`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : LiesIn x (C k)`. Use `⟨pos k hk, by simp [hk], ?_⟩` and prove the remaining obligations. Rewrite using `[hτ k hk z hz]`.

Conclude with `(hzero k z (hψW z hz)).2 hzk`. Conclude with `absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)`. Introduce and unpack `⟨hz, i, hi, h0⟩`. Use `⟨?_, hz⟩` and prove the remaining obligations. Distinguish the cases in `hk : LiesIn x (C k)`.

Simplify using `only [hk, dite_true, Option.some.injEq] at hi`. Substitute `hi` using the available equality. Rewrite `h0` using `[hτ k hk z hz]`. Conclude with `(hzero k z (hψW z hz)).1 h0`. Simplify using `[hk] at hi`.

Use `(hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_` and prove the remaining obligations. Establish `h : ∀ k, DifferentiableOn ℂ (fun v => ev Y.str σ _ (DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v)) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source)` using `fun k => ((Y.an σ).holoOn_ev _ (DivSec.eqT hn k x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle k) (hψW _ hv.2)⟩`. Establish `key : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun v => ∏ k ∈ s, ev Y.str σ _ (DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v) ^ mu k) (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using differentiableOn_const (1 : ℂ)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `((h a).pow (mu a)).mul ih`. Conclude with `(key _).congr fun v _ => rfl`.

Introduce `z hz`. Use `Finset.prod_ne_zero_iff.2 fun k hk => ?_` and prove the remaining obligations. Establish `hk' : ¬ LiesIn x (C k)` using `(Finset.mem_filter.1 hk).2`. Introduce `h`. Conclude with `(Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk' ((hzero k z (hψW z hz)).1 (pow_eq_zero_iff'.1 h).1)`.

Introduce `z hz`. Simplify using `only [wSec]`. Rewrite using `[← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun k => LiesIn x (C k))]`. Use `congr 1`. Rewrite using `[Finset.prod_filter]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : LiesIn x (C k)`. Simplify using `only [hk, if_true, τ, dite_true]`. Rewrite using `[hτ k hk z hz]`. Simplify using `[hk, τ]`.
-/
theorem isSNC_wSec {B : FinHolAtlas Y.dim (Pts Y σ)} (hB : IsAlgAtlas B) (hsnc : ∀ y : Y.X, LSncAt Y.X C y) :
    IsSNC B (wPot hn mu) (wSec hn mu) mu (fun i => {z | LiesIn z (C i)}) := by
  classical
  intro x
  let S : Finset (Fin m) := Finset.univ.filter fun i => LiesIn x (C i)
  have hS : ∀ i, i ∈ S ↔ LiesIn x (C i) := fun i => by simp [S]
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x
  let W : Y.X.Opens := Finset.univ.inf fun i => (DivSec.eqV hn i x).1
  have hWle : ∀ i, W ≤ (DivSec.eqV hn i x).1 := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (DivSec.eqV hn i x).1) ↔
      ∀ i ∈ s, z ∈ ptsIn Y.str σ (DivSec.eqV hn i x).1 := by
    intro z s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]
  have hWU : ptsIn Y.str σ W = (DivSec.divPot hn).U x := by
    ext z
    rw [hmemI z Finset.univ]
    simp only [DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]
  have hxW : x ∈ ptsIn Y.str σ W := hWU ▸ (DivSec.divPot hn).mem_U x
  let ix : Fin S.card → Fin m := fun j => (S.equivFin.symm j).1
  have hix : Function.Injective ix := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hixS : ∀ j, LiesIn x (C (ix j)) := fun j => (hS _).1 (S.equivFin.symm j).2
  let g : Fin S.card → Γ(Y.X, W) := fun j => resG Y.X (hWle (ix j)) (DivSec.eqT hn (ix j) x)
  have hgev : ∀ i z, z ∈ ptsIn Y.str σ W →
      ev Y.str σ W (resG Y.X (hWle i) (DivSec.eqT hn i x)) z = ev Y.str σ _ (DivSec.eqT hn i x) z :=
    fun i z hz => ev_res _ hz _
  have hzero : ∀ i z, z ∈ ptsIn Y.str σ W →
      (ev Y.str σ _ (DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i)) := fun i z hz =>
    ev_eq_zero_iff (DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)
  have h0 : ∀ j, ev Y.str σ W (g j) x = 0 := fun j => by
    simp only [g]; rw [hgev _ _ hxW]; exact (hzero _ _ hxW).2 (hixS j)
  have hliA := DivSec.linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => DivSec.eqV hn i x)
    (fun i => DivSec.eqT hn i x) (fun i => (DivSec.eq_spec hn i x).1) (fun i => (DivSec.eq_spec hn i x).2.1)
  have hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x)) := by
    have h2 := hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i}))
      (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))
    convert h2 using 1
    funext j
    have e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)]
        ev Y.str σ _ (DivSec.eqT hn (ix j) x) ∘ c.e.symm :=
      Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
        (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2
    simp only [Function.comp_apply]
    exact e.fderiv_eq
  have hcard : S.card ≤ Y.dim := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli
  let O : Set (Pts Y σ) := (DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}
  have hO : IsOpen O := by
    refine ((DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)
    by_cases h : LiesIn x (C k)
    · simp [h]
    · simpa [h] using isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  have hψa : ∀ z, ψ z = e z := fun z => rfl
  have hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W := fun z hz => hsub (hψs ▸ hz).1
  have hψO : ∀ z ∈ ψ.source, z ∈ O := fun z hz => (hψs ▸ hz).2
  have hcompat : IsCompatChart B ψ := by
    refine DivSec.isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_
    · intro V _ _ _ B' y hB' hy hm
      exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
    · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1
  let pos : ∀ k, LiesIn x (C k) → Fin Y.dim := fun k hk =>
    ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩
  let τ : Fin m → Option (Fin Y.dim) := fun k => if hk : LiesIn x (C k) then some (pos k hk) else none
  have hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (DivSec.eqT hn k x) z := by
    intro k hk z hz
    rw [hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]
    have hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩ := rfl
    have hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k := by simp [ix]
    rw [hj]
    simp only [g]
    rw [hgev _ _ (hψW z hz)]
    rw [hk']
  refine ⟨ψ, hcompat, hψs ▸ ⟨hx0, (DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩,
    fun z hz => (hψO z hz).1, τ, ?_, ?_, fun z => ∏ k ∈ Finset.univ.filter (fun k => ¬ LiesIn x (C k)),
      ev Y.str σ _ (DivSec.eqT hn k x) z ^ mu k, ?_, ?_, ?_⟩
  · by_cases h : LiesIn x (C k)
    · exact Or.inl h
    · exact Or.inr h
  · intro k k' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with hk hk'
    have := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩ := Fin.ext (by simpa [pos] using congrArg Fin.val this)
    exact congrArg Subtype.val (S.equivFin.injective h3)
  · intro k
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]
    constructor
    · rintro ⟨hzk, hz⟩
      refine ⟨hz, ?_⟩
      by_cases hk : LiesIn x (C k)
      · refine ⟨pos k hk, by simp [hk], ?_⟩
        rw [hτ k hk z hz]
        exact (hzero k z (hψW z hz)).2 hzk
      · exact absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)
    · rintro ⟨hz, i, hi, h0⟩
      refine ⟨?_, hz⟩
      by_cases hk : LiesIn x (C k)
      · simp only [hk, dite_true, Option.some.injEq] at hi
        subst hi
        rw [hτ k hk z hz] at h0
        exact (hzero k z (hψW z hz)).1 h0
      · simp [hk] at hi
  · refine (hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_
    have h : ∀ k, DifferentiableOn ℂ (fun v => ev Y.str σ _ (DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v))
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := fun k =>
      ((Y.an σ).holoOn_ev _ (DivSec.eqT hn k x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle k) (hψW _ hv.2)⟩
    have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
        (fun v => ∏ k ∈ s, ev Y.str σ _ (DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v) ^ mu k)
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using differentiableOn_const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((h a).pow (mu a)).mul ih
    exact (key _).congr fun v _ => rfl
  · intro z hz
    refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
    have hk' : ¬ LiesIn x (C k) := (Finset.mem_filter.1 hk).2
    intro h
    exact (Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk' ((hzero k z (hψW z hz)).1 (pow_eq_zero_iff'.1 h).1)
  · intro z hz
    simp only [wSec]
    rw [← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun k => LiesIn x (C k))]
    congr 1
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : LiesIn x (C k)
    · simp only [hk, if_true, τ, dite_true]
      rw [hτ k hk z hz]
    · simp [hk, τ]

omit [NumberField F] in

/- English proof (translation)
Establish `h1 : ∀ i j, RegAt (under z) (a i ^ j) ∧ ratVal (a i ^ j) z = ratVal (a i) z ^ j` using `fun i j => by`. Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `⟨(unitAt_one _).regAt, Base.ratVal_one _⟩`. Consider the case `succ j ih => rw [pow_succ, pow_succ, ratVal_mul ih.1 (ha i), ih.2]`.

Conclude with `⟨ih.1.mul (ha i), rfl⟩`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.prod_empty]`. Conclude with `⟨(unitAt_one _).regAt, Base.ratVal_one _⟩`. Consider the case `insert b s hb ih`.

Rewrite using `[Finset.prod_insert hb, Finset.prod_insert hb, ratVal_mul (h1 _ _).1 ih.1, ih.2, (h1 _ _).2]`. Conclude with `⟨(h1 _ _).1.mul ih.1, rfl⟩`.
-/
theorem ratVal_prod_pow {ι : Type} {z : Pts Y σ} (a : ι → Y.Fn) (k : ι → ℕ) (ha : ∀ i, RegAt (under z) (a i)) (s : Finset ι) :
    RegAt (under z) (∏ i ∈ s, a i ^ k i) ∧ ratVal (∏ i ∈ s, a i ^ k i) z = ∏ i ∈ s, ratVal (a i) z ^ k i := by
  classical
  have h1 : ∀ i j, RegAt (under z) (a i ^ j) ∧ ratVal (a i ^ j) z = ratVal (a i) z ^ j := fun i j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact ⟨(unitAt_one _).regAt, Base.ratVal_one _⟩
    | succ j ih => rw [pow_succ, pow_succ, ratVal_mul ih.1 (ha i), ih.2]; exact ⟨ih.1.mul (ha i), rfl⟩
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact ⟨(unitAt_one _).regAt, Base.ratVal_one _⟩
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, ratVal_mul (h1 _ _).1 ih.1, ih.2, (h1 _ _).2]
    exact ⟨(h1 _ _).1.mul ih.1, rfl⟩

variable {mu} {Δ : Y.Dv}
  (hΔ : ∀ y : Y.X, ∃ (g : Y.Fnˣ) (r : Y.X.presheaf.stalk y), Δ.IsEqn y g ∧ algebraMap _ Y.X.functionField r = (g : Y.Fn) ∧
    Ideal.span {r} = ∏ i, stalkId (Scheme.IdealSheafData.vanishingIdeal (C i)) y ^ mu i)

include hΔ in

/- English proof (translation)
Establish `hg : ∀ i, genericPoint Y.X ∈ (DivSec.eqV hn i x).1` using `fun i => gen_mem (mem_ptsIn.1 (DivSec.eq_spec hn i x).1)`. Set `a : Y.Fn` to `∏ i, fnOf _ (hg i) (DivSec.eqT hn i x) ^ mu i`. Establish `key : ∀ z ∈ (DivSec.divPot hn).U x, ∃ g : Y.Fnˣ, Δ.IsEqn (under z) g ∧ UnitAt (under z) (a / g)` using `fun z hz => by`. Take `⟨g, r, h₁, h₂, h₃⟩` from `hΔ (under z)`. Establish `hz' : ∀ i, under z ∈ (DivSec.eqV hn i x).1` using `fun i => mem_ptsIn.1 (DivSec.mem_eqV hn hz i)`.

Establish `h₄ : ∀ i, stalkId (Scheme.IdealSheafData.vanishingIdeal (C i)) (under z) ^ mu i = Ideal.span {Y.X.presheaf.germ _ _ (hz' i) (DivSec.eqT hn i x) ^ mu i}` using `fun i => by`. Rewrite using `[ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ _ (DivSec.eqV hn i x) (hz' i), (DivSec.eq_spec hn i x).2.1, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]`. Rewrite `h₃` using `[Finset.prod_congr rfl fun i _ => h₄ i, Ideal.prod_span_singleton, Ideal.span_singleton_eq_span_singleton]`. Take `⟨u, hu⟩` from `h₃`. Use `⟨g, h₁, u, u.isUnit, (eq_div_iff g.ne_zero).2 ?_⟩` and prove the remaining obligations.

Rewrite using `[← h₂, ← map_mul, mul_comm, hu, map_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [map_pow, algebraMap_germ]`. Establish `ha : a ≠ 0`. Take `⟨g, -, h⟩` from `key x ((DivSec.divPot hn).mem_U x)`. Conclude with `(div_ne_zero_iff.1 h.ne_zero).1`.

Use `⟨Units.mk0 a ha, fun z hz => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨g, h₁, h₂⟩` from `key z hz`. Conclude with `h₁.iff_unitAt.2 h₂`. Use `(ratVal_prod_pow _ mu (fun i => regAt_fnOf (mem_ptsIn.1 (DivSec.mem_eqV hn hz i)) _ _) Finset.univ).2.trans ?_` and prove the remaining obligations. Conclude with `Finset.prod_congr rfl fun i _ => by rw [ratVal_fnOf (DivSec.mem_eqV hn hz i)]`.
-/
theorem exists_eqn (x : Pts Y σ) : ∃ e : Y.Fnˣ, ∀ z ∈ (DivSec.divPot hn).U x,
    z ∈ Var.eqnSet σ Δ e ∧ ratVal (e : Y.Fn) z = wSec hn mu x z := by
  have hg : ∀ i, genericPoint Y.X ∈ (DivSec.eqV hn i x).1 := fun i => gen_mem (mem_ptsIn.1 (DivSec.eq_spec hn i x).1)
  let a : Y.Fn := ∏ i, fnOf _ (hg i) (DivSec.eqT hn i x) ^ mu i
  have key : ∀ z ∈ (DivSec.divPot hn).U x, ∃ g : Y.Fnˣ, Δ.IsEqn (under z) g ∧ UnitAt (under z) (a / g) := fun z hz => by
    obtain ⟨g, r, h₁, h₂, h₃⟩ := hΔ (under z)
    have hz' : ∀ i, under z ∈ (DivSec.eqV hn i x).1 := fun i => mem_ptsIn.1 (DivSec.mem_eqV hn hz i)
    have h₄ : ∀ i, stalkId (Scheme.IdealSheafData.vanishingIdeal (C i)) (under z) ^ mu i =
        Ideal.span {Y.X.presheaf.germ _ _ (hz' i) (DivSec.eqT hn i x) ^ mu i} := fun i => by
      rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ _ (DivSec.eqV hn i x) (hz' i), (DivSec.eq_spec hn i x).2.1,
        Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    rw [Finset.prod_congr rfl fun i _ => h₄ i, Ideal.prod_span_singleton, Ideal.span_singleton_eq_span_singleton] at h₃
    obtain ⟨u, hu⟩ := h₃
    refine ⟨g, h₁, u, u.isUnit, (eq_div_iff g.ne_zero).2 ?_⟩
    rw [← h₂, ← map_mul, mul_comm, hu, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [map_pow, algebraMap_germ]
  have ha : a ≠ 0 := by
    obtain ⟨g, -, h⟩ := key x ((DivSec.divPot hn).mem_U x)
    exact (div_ne_zero_iff.1 h.ne_zero).1
  refine ⟨Units.mk0 a ha, fun z hz => ⟨?_, ?_⟩⟩
  · obtain ⟨g, h₁, h₂⟩ := key z hz
    exact h₁.iff_unitAt.2 h₂
  · refine (ratVal_prod_pow _ mu (fun i => regAt_fnOf (mem_ptsIn.1 (DivSec.mem_eqV hn hz i)) _ _) Finset.univ).2.trans ?_
    exact Finset.prod_congr rfl fun i _ => by rw [ratVal_fnOf (DivSec.mem_eqV hn hz i)]

/- English proof (translation)
Set `Z : Closeds Y.X` to `⟨⋃ i, (C i : Set Y.X), isClosed_iUnion_of_finite fun i => (C i).isClosed⟩`. Establish `hO` using `((DivSec.divPot hn).isOpen_U x).inter ((DivSec.divPot hn).isOpen_U x')`. Establish `hdense : Dense {z : Pts Y σ | ¬ LiesIn z Z}`. Establish `hd` using `(CxPtsDense.nonempty_and_dense F Y σ).2 Z.compl ⟨genericPoint Y.X, fun h => have ⟨i, hi⟩ := Set.mem_iUnion.1 h; hgen i hi⟩`. Establish `hs : ptsIn Y.str σ Z.compl = {z : Pts Y σ | ¬ LiesIn z Z}` using `Set.ext fun z => mem_ptsIn (U := Z.compl)`.

Rewrite `hd` using `[hs]`. Then use the resulting hypothesis. Establish `c₁ : ∀ x, ContinuousOn (fun z => Real.exp (-(wPot hn mu).φ x z)) ((DivSec.divPot hn).U x)` using `fun x => ((smoothOn_wPot hn mu x).continuousOn ((DivSec.divPot hn).isOpen_U x)).neg.rexp`. Establish `c₂ : ContinuousOn (Var.tv e e') ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x')` using `((Var.holoOn_tv Δ e e').mono fun w hw => ⟨(he w hw.1).1, (he' w hw.2).1⟩).continuousOn hO`. Establish `hall : Set.EqOn (fun z => Real.exp (-(wPot hn mu).φ x z)) (fun z => ‖Var.tv e e' z‖ * Real.exp (-(wPot hn mu).φ x' z)) ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x')`. Use `Set.EqOn.of_subset_closure (s := ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x') ∩ {z | ¬ LiesIn z Z}) ?_ ((c₁ x).mono Set.inter_subset_left) (c₂.norm.mul ((c₁ x').mono Set.inter_subset_right)) Set.inter_subset_left (hdense.open_subset_closure_inter hO)` and prove the remaining obligations.

Introduce and unpack `w ⟨hw, hwZ⟩`. Establish `h0 : wSec hn mu x w ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ fun h => hwZ (Set.mem_iUnion.2 ⟨i, (ev_eq_zero_iff (DivSec.eq_spec hn i x).2.1 (DivSec.mem_eqV hn hw.1 i)).1 h⟩)`. Establish `h1` using `Var.fval_trans (he w hw.1).1 (he' w hw.2).1 (Y.cx σ 1)`. Rewrite `h1` using `[Var.fval_cx, Var.fval_cx, one_mul, one_mul, (he w hw.1).2, (he' w hw.2).2]`. Establish `h2` using `(norm_wSec_mul hn mu hw.1).trans (norm_wSec_mul hn mu hw.2).symm`.

Rewrite `h2` using `[h1, norm_mul, mul_comm ‖Var.tv e e' w‖, mul_assoc]`. Conclude with `mul_left_cancel₀ (norm_ne_zero_iff.2 h0) h2`. Conclude with `hall ⟨hz, hz'⟩`.
-/
theorem exp_wPot_trans (hgen : ∀ i, genericPoint Y.X ∉ C i) {x x' : Pts Y σ} {e e' : Y.Fnˣ}
    (he : ∀ z ∈ (DivSec.divPot hn).U x, z ∈ Var.eqnSet σ Δ e ∧ ratVal (e : Y.Fn) z = wSec hn mu x z)
    (he' : ∀ z ∈ (DivSec.divPot hn).U x', z ∈ Var.eqnSet σ Δ e' ∧ ratVal (e' : Y.Fn) z = wSec hn mu x' z)
    {z : Pts Y σ} (hz : z ∈ (DivSec.divPot hn).U x) (hz' : z ∈ (DivSec.divPot hn).U x') :
    Real.exp (-(wPot hn mu).φ x z) = ‖Var.tv e e' z‖ * Real.exp (-(wPot hn mu).φ x' z) := by
  let Z : Closeds Y.X := ⟨⋃ i, (C i : Set Y.X), isClosed_iUnion_of_finite fun i => (C i).isClosed⟩
  have hO := ((DivSec.divPot hn).isOpen_U x).inter ((DivSec.divPot hn).isOpen_U x')
  have hdense : Dense {z : Pts Y σ | ¬ LiesIn z Z} := by
    have hd := (CxPtsDense.nonempty_and_dense F Y σ).2 Z.compl
      ⟨genericPoint Y.X, fun h => have ⟨i, hi⟩ := Set.mem_iUnion.1 h; hgen i hi⟩
    have hs : ptsIn Y.str σ Z.compl = {z : Pts Y σ | ¬ LiesIn z Z} :=
      Set.ext fun z => mem_ptsIn (U := Z.compl)
    rwa [hs] at hd
  have c₁ : ∀ x, ContinuousOn (fun z => Real.exp (-(wPot hn mu).φ x z)) ((DivSec.divPot hn).U x) := fun x =>
    ((smoothOn_wPot hn mu x).continuousOn ((DivSec.divPot hn).isOpen_U x)).neg.rexp
  have c₂ : ContinuousOn (Var.tv e e') ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x') :=
    ((Var.holoOn_tv Δ e e').mono fun w hw => ⟨(he w hw.1).1, (he' w hw.2).1⟩).continuousOn hO
  have hall : Set.EqOn (fun z => Real.exp (-(wPot hn mu).φ x z))
      (fun z => ‖Var.tv e e' z‖ * Real.exp (-(wPot hn mu).φ x' z))
      ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x') := by
    refine Set.EqOn.of_subset_closure (s := ((DivSec.divPot hn).U x ∩ (DivSec.divPot hn).U x') ∩ {z | ¬ LiesIn z Z})
      ?_ ((c₁ x).mono Set.inter_subset_left) (c₂.norm.mul ((c₁ x').mono Set.inter_subset_right))
      Set.inter_subset_left (hdense.open_subset_closure_inter hO)
    rintro w ⟨hw, hwZ⟩
    have h0 : wSec hn mu x w ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ fun h =>
      hwZ (Set.mem_iUnion.2 ⟨i, (ev_eq_zero_iff (DivSec.eq_spec hn i x).2.1 (DivSec.mem_eqV hn hw.1 i)).1 h⟩)
    have h1 := Var.fval_trans (he w hw.1).1 (he' w hw.2).1 (Y.cx σ 1)
    rw [Var.fval_cx, Var.fval_cx, one_mul, one_mul, (he w hw.1).2, (he' w hw.2).2] at h1
    have h2 := (norm_wSec_mul hn mu hw.1).trans (norm_wSec_mul hn mu hw.2).symm
    rw [h1, norm_mul, mul_comm ‖Var.tv e e' w‖, mul_assoc] at h2
    exact mul_left_cancel₀ (norm_ne_zero_iff.2 h0) h2
  exact hall ⟨hz, hz'⟩

include hΔ in

/- English proof (translation)
Use `choose e he using exists_eqn hn hΔ`. Establish `ht` using `fun x x' z => exp_wPot_trans hn hgen (he x) (he x') (z := z)`. Use `⟨⟨fun x => (hB.smoothOn_iff (Y.an σ) ((DivSec.divPot hn).isOpen_U x)).2 (smoothOn_wPot hn mu x), fun x x' y hy => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hO` using `((DivSec.divPot hn).isOpen_U x').inter ((DivSec.divPot hn).isOpen_U x)`. Take `⟨W, hW, hyW, hWs, G, hG, hGre⟩` from `((Var.holoOn_tv Δ (e x') (e x)).mono fun w hw => ⟨(he x' w hw.1).1, (he x w hw.2).1⟩).exists_log hO ⟨hy.2, hy.1⟩ (Var.tv_ne_zero (he x' y hy.2).1 (he x y hy.1).1)`.

Use `⟨W, hW, hyW, G, (hB.holoOn_iff (Y.an σ) hW).2 hG, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Real.log (ht x' x z hz.2 hz.1.2)`. Rewrite `h1` using `[Real.log_mul (norm_ne_zero_iff.2 (Var.tv_ne_zero (he x' z hz.2).1 (he x z hz.1.2).1)) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]`. Rewrite using `[hGre z hz.1.1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `M : Var.Met Y σ Δ` to `Var.Met.ofCover (DivSec.divPot hn).U e (fun y => ⟨y, (DivSec.divPot hn).mem_U y⟩) (fun x z => Real.exp (-(wPot hn mu).φ x z) ^ 2) fun _ _ => sq_nonneg _`. Establish `hM : ∀ x, ∀ z ∈ (DivSec.divPot hn).U x, M.h (e x) z = Real.exp (-(wPot hn mu).φ x z) ^ 2` using `fun x z hz => Var.Met.ofCover_h _ _ (fun x z hz => (he x z hz).1) _ _ _ (fun x x' z hz hz' => by rw [ht x x' z hz hz', mul_pow]) hz`. Establish `hpos : M.posSet = Set.univ` using `Set.eq_univ_of_forall fun z => (Var.Met.mem_posSet_iff (he z z ((DivSec.divPot hn).mem_U z)).1).2 (by rw [hM z z ((DivSec.divPot hn).mem_U z)]; positivity)`. Use `⟨M, fun x => ⟨((e x)⁻¹ : Y.Fnˣ), fun z hz => ⟨?_, posAt_of_posSet hpos _, ?_⟩⟩⟩` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val]`.

Conclude with `CartierDiv.isEqn_iff_generatesAt_inv.1 (he x z hz).1`. Establish `h1 : (cxSt F).pn Y σ Δ M ((cxSt F).cx Y σ ((e x)⁻¹ : Y.Fnˣ)) z = _` using `(Var.pn_frame (he x z hz).1).trans (hM x z hz)`. Simplify using `only [lnN, id]`. Rewrite using `[h1, Real.log_pow, Real.log_exp]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_met {B : FinHolAtlas Y.dim (Pts Y σ)} (hB : IsAlgAtlas B) (hgen : ∀ i, genericPoint Y.X ∉ C i) :
    IsPotential B (wPot hn mu) ∧ ∃ M : (cxSt F).Met Y σ Δ, IsPot id M (wPot hn mu) := by
  choose e he using exists_eqn hn hΔ
  have ht := fun x x' z => exp_wPot_trans hn hgen (he x) (he x') (z := z)
  refine ⟨⟨fun x => (hB.smoothOn_iff (Y.an σ) ((DivSec.divPot hn).isOpen_U x)).2 (smoothOn_wPot hn mu x),
    fun x x' y hy => ?_⟩, ?_⟩
  · have hO := ((DivSec.divPot hn).isOpen_U x').inter ((DivSec.divPot hn).isOpen_U x)
    obtain ⟨W, hW, hyW, hWs, G, hG, hGre⟩ :=
      ((Var.holoOn_tv Δ (e x') (e x)).mono fun w hw => ⟨(he x' w hw.1).1, (he x w hw.2).1⟩).exists_log hO ⟨hy.2, hy.1⟩
        (Var.tv_ne_zero (he x' y hy.2).1 (he x y hy.1).1)
    refine ⟨W, hW, hyW, G, (hB.holoOn_iff (Y.an σ) hW).2 hG, fun z hz => ?_⟩
    have h1 := congrArg Real.log (ht x' x z hz.2 hz.1.2)
    rw [Real.log_mul (norm_ne_zero_iff.2 (Var.tv_ne_zero (he x' z hz.2).1 (he x z hz.1.2).1)) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp] at h1
    rw [hGre z hz.1.1]
    linarith
  · let M : Var.Met Y σ Δ := Var.Met.ofCover (DivSec.divPot hn).U e (fun y => ⟨y, (DivSec.divPot hn).mem_U y⟩)
      (fun x z => Real.exp (-(wPot hn mu).φ x z) ^ 2) fun _ _ => sq_nonneg _
    have hM : ∀ x, ∀ z ∈ (DivSec.divPot hn).U x, M.h (e x) z = Real.exp (-(wPot hn mu).φ x z) ^ 2 := fun x z hz =>
      Var.Met.ofCover_h _ _ (fun x z hz => (he x z hz).1) _ _ _
        (fun x x' z hz hz' => by rw [ht x x' z hz hz', mul_pow]) hz
    have hpos : M.posSet = Set.univ := Set.eq_univ_of_forall fun z =>
      (Var.Met.mem_posSet_iff (he z z ((DivSec.divPot hn).mem_U z)).1).2
        (by rw [hM z z ((DivSec.divPot hn).mem_U z)]; positivity)
    refine ⟨M, fun x => ⟨((e x)⁻¹ : Y.Fnˣ), fun z hz => ⟨?_, posAt_of_posSet hpos _, ?_⟩⟩⟩
    · rw [Units.val_inv_eq_inv_val]
      exact CartierDiv.isEqn_iff_generatesAt_inv.1 (he x z hz).1
    · have h1 : (cxSt F).pn Y σ Δ M ((cxSt F).cx Y σ ((e x)⁻¹ : Y.Fnˣ)) z = _ :=
        (Var.pn_frame (he x z hz).1).trans (hM x z hz)
      simp only [lnN, id]
      rw [h1, Real.log_pow, Real.log_exp]
      push_cast
      ring

end An

/- English proof (translation)
Substitute `hdim` using the available equality. Establish `hA : DivSec.ChartsAlg (M.A a) (I.pt a)` using `I.alg a`. Establish `hB` using `DivSec.isAlgAtlas_algAtlas hA`. Take `⟨h₁, μ, h₂⟩` from `exists_met hn hΔ hB (generic_notMem hsnc)`. Conclude with `⟨μ, (wPot hn mu).pullback (I.pt a) (I.pt a).continuous, fun x w => wSec hn mu (I.pt a x) (I.pt a w), fun x => h₂ (I.pt a x) |>.imp fun f hf y hy => hf (I.pt a y) hy, DivSec.isPotential_pullback hA h₁, DivSec.isSection_pullback hA (isSection_wSec hn mu hB), DivSec.isSNC_pullback h …`.
-/
theorem exists_snc_section {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    (a : Fin (M.n + 1)) {m : ℕ} {C : Fin m → Closeds Y.X} {n : Fin m → Pts Y (I.ε a) → ℝ} (hdim : Y.dim = e)
    (hsnc : ∀ y : Y.X, LSncAt Y.X C y) (hn : ∀ i, IsDivNorm (Y.an (I.ε a)) (C i) (n i)) {mu : Fin m → ℕ} {Δ : Y.Dv}
    (hΔ : ∀ y : Y.X, ∃ (g : Y.Fnˣ) (r : Y.X.presheaf.stalk y), Δ.IsEqn y g ∧ algebraMap _ Y.X.functionField r = (g : Y.Fn) ∧
      Ideal.span {r} = ∏ i, stalkId (Scheme.IdealSheafData.vanishingIdeal (C i)) y ^ mu i) :
    ∃ (μ : (cxSt F).Met Y (I.ε a) Δ) (L : LocPot (M.X a)) (s : M.X a → M.X a → ℂ), IsPot (I.pt a) μ L ∧
      IsPotential (M.A a) L ∧ IsSection (M.A a) L s ∧ IsSNC (M.A a) L s mu fun i => {z | under (I.pt a z) ∈ C i} := by
  subst hdim
  have hA : DivSec.ChartsAlg (M.A a) (I.pt a) := I.alg a
  have hB := DivSec.isAlgAtlas_algAtlas hA
  obtain ⟨h₁, μ, h₂⟩ := exists_met hn hΔ hB (generic_notMem hsnc)
  exact ⟨μ, (wPot hn mu).pullback (I.pt a) (I.pt a).continuous, fun x w => wSec hn mu (I.pt a x) (I.pt a w),
    fun x => h₂ (I.pt a x) |>.imp fun f hf y hy => hf (I.pt a y) hy, DivSec.isPotential_pullback hA h₁,
    DivSec.isSection_pullback hA (isSection_wSec hn mu hB), DivSec.isSNC_pullback hA (isSNC_wSec hn mu hB hsnc)⟩

/- English proof (translation)
Take `⟨j, hj⟩` from `B.exists_mem ((π ≫ ι) y)`. Use `⟨_, Y.presheaf.germ ((π ≫ ι) ⁻¹ᵁ B.U j) y hj ((π ≫ ι).app _ (B.f j)) ^ b, (isEqn_pullDiv B (π ≫ ι) h j hj).nsmul b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, Units.val_pow_eq_pow_val]`. Conclude with `congrArg (· ^ b) (algebraMap_germ (U := (π ≫ ι) ⁻¹ᵁ B.U j) hj _)`. Establish `h1` using `GlobalTheory.VanStalk.stalkId_comap (π ≫ ι) B.idealSheaf y`.

Rewrite `h1` using `[B.stalkId_idealSheaf j _ hj, Ideal.map_span, Set.image_singleton, Scheme.Hom.germ_stalkMap_apply, Scheme.IdealSheafData.comap_comp, GlobalTheory.VanStalk.stalkId_comap, hmu, ← Ideal.mapHom_apply, map_prod]`. Rewrite using `[← Ideal.span_singleton_pow, ← h1, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, Ideal.mapHom_apply, pow_mul, stalkId_preimage p π y (hsnc _)]`.
-/
theorem eqn_pullDiv {k : Type} [Field k] {X Y Z : Scheme.{0}} [IsIntegral Y] (p : X ⟶ Sp k) [Smooth p] (π : Y ⟶ X) [Smooth π]
    (ι : X ⟶ Z) (B : EffCartierData Z) (h : (π ≫ ι) (genericPoint Y) ∉ B.idealSheaf.support) {m : ℕ} {C : Fin m → Closeds X}
    (hsnc : ∀ x, LSncAt X C x) {mu : Fin m → ℕ}
    (hmu : ∀ x, stalkId (B.idealSheaf.comap ι) x = ∏ i, stalkId (Scheme.IdealSheafData.vanishingIdeal (C i)) x ^ mu i)
    (b : ℕ) (y : Y) : ∃ (g : Y.functionFieldˣ) (r : Y.presheaf.stalk y), (b • pullDiv B (π ≫ ι) h).IsEqn y g ∧
      algebraMap _ Y.functionField r = (g : Y.functionField) ∧ Ideal.span {r} =
        ∏ i, stalkId (Scheme.IdealSheafData.vanishingIdeal ((C i).preimage π.continuous)) y ^ (mu i * b) := by
  obtain ⟨j, hj⟩ := B.exists_mem ((π ≫ ι) y)
  refine ⟨_, Y.presheaf.germ ((π ≫ ι) ⁻¹ᵁ B.U j) y hj ((π ≫ ι).app _ (B.f j)) ^ b,
    (isEqn_pullDiv B (π ≫ ι) h j hj).nsmul b, ?_, ?_⟩
  · rw [map_pow, Units.val_pow_eq_pow_val]
    exact congrArg (· ^ b) (algebraMap_germ (U := (π ≫ ι) ⁻¹ᵁ B.U j) hj _)
  · have h1 := GlobalTheory.VanStalk.stalkId_comap (π ≫ ι) B.idealSheaf y
    rw [B.stalkId_idealSheaf j _ hj, Ideal.map_span, Set.image_singleton, Scheme.Hom.germ_stalkMap_apply,
      Scheme.IdealSheafData.comap_comp, GlobalTheory.VanStalk.stalkId_comap, hmu, ← Ideal.mapHom_apply, map_prod] at h1
    rw [← Ideal.span_singleton_pow, ← h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, Ideal.mapHom_apply, pow_mul, stalkId_preimage p π y (hsnc _)]

end GlobalTheory.BdSec

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.BdSec

open AlgebraicGeometry in

/- English proof (translation)
Introduce `_ _ D O x P _ A T H R c a`. Establish `hπ` using `GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c`. Establish `: Smooth (GlobalTheory.Toroidal.genStr O.s.T.Z)` using `SmoothOfRelativeDimension.smooth O.S.Dw.dim _`. Establish `: IsLocallyNoetherian (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0})` using `LocallyOfFiniteType.isLocallyNoetherian (GlobalTheory.Toroidal.genStr O.s.T.Z)`. Use `GlobalTheory.Toroidal.isProper_genStr O.s.T.Z` as an intermediate fact.

Establish `: CompactSpace (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0})` using `QuasiCompact.compactSpace_of_compactSpace (GlobalTheory.Toroidal.genStr O.s.T.Z)`. Establish `: IsNoetherian (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0})` using `{}`. Establish `hsnc` using `GlobalTheory.SncLocal.lSncAt_of_snc _ _ _ _ O.s.T.snc x.cpt_list`. Establish `hsupp : ((O.s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι O.s.T.Z)).support : Set (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0})) = GlobalTheory.Toroidal.genBd O.s.T.Z`. Rewrite using `[Scheme.IdealSheafData.support_comap]`.

Use extensionality with `y`. Conclude with `⟨fun h => GlobalTheory.Toroidal.mem_genBd_iff.2 (O.s.T.BD_supp _ h), O.s.T.BD_pos _⟩`. Take `⟨mu, hmu₁, hmu⟩` from `exists_mult (O.s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι O.s.T.Z)) (hsupp ▸ x.cpt_list) hsnc fun y => by`. Take `⟨j, hj⟩` from `O.s.T.BD.exists_mem (GlobalTheory.Toroidal.genι O.s.T.Z y)`. Rewrite using `[GlobalTheory.VanStalk.stalkId_comap, O.s.T.BD.stalkId_idealSheaf j _ hj, Ideal.map_span, Set.image_singleton]`.

Conclude with `⟨_, rfl⟩`. Take `⟨μ, L, s, h₁, h₂, h₃, h₄⟩` from `exists_snc_section (R.man c) a (C := fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous) (n := fun i z => x.nrm _ i ((O.Φ.C c).down z)) (mu := fun i => mu i * P.b) (Δ := P.bd c) (O.dim_eq c) (fun y => GlobalTheory.SncPull.lsncAt_preimage _ _ _ (GlobalTheory.Toroidal.genStr O.s.T. …`. Use `⟨μ, L, s, h₁, h₂, h₃, _, _, _, h₄, fun i => Nat.mul_pos (hmu₁ i) P.b_pos, Set.ext fun z => ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iUnion.trans (((R.an c).Z a z).trans (x.liesIn_genBd_iff ((O.Φ.C c).down ((R.man c).pt a z)))).symm`.
-/
theorem exists_bd_section : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (R : O.Reads A T H) (c : O.s.Comp) (σ : Fin ((T.M c).n + 1)), ∃ (m : (GlobalTheory.TrueGeo.cxSt D.what₂.LL).Met (O.var c) ((R.man c).ε σ) (P.bd c)) (L : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)) (s : (T.M c).X σ → (T.M c).X σ → ℂ), IsPot ((R.man c).pt σ) m L ∧ ReciprocityTheory.AnForm.M.IsPotential ((T.M c).A σ) L ∧ ReciprocityTheory.AnForm.M.IsSection ((T.M c).A σ) L s ∧ ∃ (n : ℕ) (mu : Fin n → ℕ) (W : Fin n → Set ((T.M c).X σ)), ReciprocityTheory.AnForm.M.IsSNC ((T.M c).A σ) L s mu W ∧ (∀ i, 1 ≤ mu i) ∧ ⋃ i, W i = (T.M c).Z σ := by
  intro _ _ D O x P _ A T H R c a
  have hπ := GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c
  have : Smooth (GlobalTheory.Toroidal.genStr O.s.T.Z) := SmoothOfRelativeDimension.smooth O.S.Dw.dim _
  have : IsLocallyNoetherian (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (GlobalTheory.Toroidal.genStr O.s.T.Z)
  have := GlobalTheory.Toroidal.isProper_genStr O.s.T.Z
  have : CompactSpace (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (GlobalTheory.Toroidal.genStr O.s.T.Z)
  have : IsNoetherian (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0}) := {}
  have hsnc := GlobalTheory.SncLocal.lSncAt_of_snc _ _ _ _ O.s.T.snc x.cpt_list
  have hsupp : ((O.s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι O.s.T.Z)).support : Set (GlobalTheory.Toroidal.gen O.s.T.Z : Scheme.{0})) =
      GlobalTheory.Toroidal.genBd O.s.T.Z := by
    rw [Scheme.IdealSheafData.support_comap]
    ext y
    exact ⟨fun h => GlobalTheory.Toroidal.mem_genBd_iff.2 (O.s.T.BD_supp _ h), O.s.T.BD_pos _⟩
  obtain ⟨mu, hmu₁, hmu⟩ := exists_mult (O.s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι O.s.T.Z)) (hsupp ▸ x.cpt_list) hsnc
    fun y => by
      obtain ⟨j, hj⟩ := O.s.T.BD.exists_mem (GlobalTheory.Toroidal.genι O.s.T.Z y)
      rw [GlobalTheory.VanStalk.stalkId_comap, O.s.T.BD.stalkId_idealSheaf j _ hj, Ideal.map_span, Set.image_singleton]
      exact ⟨_, rfl⟩
  obtain ⟨μ, L, s, h₁, h₂, h₃, h₄⟩ := exists_snc_section (R.man c) a
    (C := fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous) (n := fun i z => x.nrm _ i ((O.Φ.C c).down z))
    (mu := fun i => mu i * P.b) (Δ := P.bd c) (O.dim_eq c)
    (fun y => GlobalTheory.SncPull.lsncAt_preimage _ _ _ (GlobalTheory.Toroidal.genStr O.s.T.Z) _ _ _ y (hsnc _))
    (fun i => GlobalTheory.DivPullback.isDivNorm_flag D _ _ _ _ _ O.s O.Φ c _ _ _ hπ (x.nrm_div _ i))
    (eqn_pullDiv (GlobalTheory.Toroidal.genStr O.s.T.Z) (O.Φ.C c).π _ O.s.T.BD _ hsnc hmu P.b)
  refine ⟨μ, L, s, h₁, h₂, h₃, _, _, _, h₄, fun i => Nat.mul_pos (hmu₁ i) P.b_pos, Set.ext fun z => ?_⟩
  exact Set.mem_iUnion.trans
    (((R.an c).Z a z).trans (x.liesIn_genBd_iff ((O.Φ.C c).down ((R.man c).pt a z)))).symm

end GlobalTheory.BdSec
