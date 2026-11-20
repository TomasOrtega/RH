import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

/- English proof (translation)
Introduce `O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 x m hx`. Take `⟨⟨c, hc⟩, hcx⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin j)) x`. Establish `hc0 : c ≠ 0` using `nonZeroDivisors.ne_zero hc`. Establish `hcx' : ∀ a, ∃ t : O, algebraMap O (FractionRing O) t = c • x a` using `fun a => RingHom.mem_rangeS.mp (hcx a (Finset.mem_univ a))`. Use `choose y hy using hcx'`.

Take `⟨v, rfl⟩` from `hq m`. Take `⟨d, hd0, hw'⟩` from `hsat (c • v)`. Take `⟨w, hw⟩` from `LinearMap.mem_range.mp hw'`. Establish `he0 : d * c ≠ 0` using `mul_ne_zero hd0 hc0`. Establish `hK0 : algebraMap O (FractionRing O) (d * c) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr he0`.

Establish `cancelV : ∀ u u' : V, (d * c) • u = (d * c) • u' → u = u'`. Introduce `u u' h`. Rewrite `h` using `[← algebraMap_smul (FractionRing O) (d * c) u, ← algebraMap_smul (FractionRing O) (d * c) u']`. Conclude with `smul_right_injective V hK0 h`. Establish `cancelL : ∀ a b : L, (d * c) • a = (d * c) • b → a = b`.

Introduce `a b h`. Apply `hi` to reduce the goal to its premises. Apply `cancelV` to reduce the goal to its premises. Establish `h'` using `congrArg i h`. Rewrite `h'` using `[map_smul, map_smul]`. Then use the resulting hypothesis.

Establish `hf : ∀ g : D, ∃ zg : L, i zg = ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v)`. Introduce `g`. Establish `hmem : ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) ∈ LinearMap.ker q`. Rewrite using `[LinearMap.mem_ker, map_sub, map_sub, hx g, hqρ]`. Conclude with `sub_self _`.

Rewrite `hmem` using `[hker]`. Conclude with `LinearMap.mem_range.mp hmem`. Use `choose z hz using hf`. Take `⟨Y, hYdef⟩ : ∃ Y : coZ1s ρL, Y = ∑ a, (d * y a) • κ a - cobZ ρL w` from `⟨_, rfl⟩`. Establish `hYg : ∀ g, (Y : D → L) g = ∑ a, (d * y a) • (κ a : D → L) g - (ρL g w - w)`.

Introduce `g`. Rewrite using `[hYdef, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]`. Both sides reduce to the same expression. Establish `hY : ∀ g, (d * c) • z g = (Y : D → L) g`. Introduce `g`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hYg g, map_smul, hz g, map_sub, map_sub, map_sum, hiρ, hw, smul_sub, smul_sub, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, mul_smul, mul_smul, ← smul_assoc c (x a), ← hy a, algebraMap_smul]`.

Rewrite using `[LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, mul_smul, mul_smul]`. Establish `hzc : z ∈ coZ1s ρL` using `by show ∀ g h, z (g * h) = z g + ρL g (z h)`. Introduce `g h`. Apply `cancelL` to reduce the goal to its premises. Rewrite using `[smul_add, ← map_smul, hY, hY, hY]`.

Conclude with `Y.2 g h`. Establish `hZY : (d * c) • (⟨z, hzc⟩ : coZ1s ρL) = Y` using `Subtype.ext (funext hY)`. Establish `hYcl : (Submodule.mkQ _ Y : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL)`. Rewrite using `[hYdef, map_sub, mkQ_cobZ, sub_zero, map_sum]`. Simplify using `only [map_smul]`.

Establish `h2 : (d * c) • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL)`. Rewrite using `[← map_smul, hZY, hYcl]`. Establish `hZF : (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) ∈ Ff`. Apply `hF1 (d * c) _ he0` to reduce the goal to its premises. Rewrite using `[h2]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hF2 a)`. Take `⟨b, c', hc'0, hc'⟩` from `hF3 _ hZF`. Establish `h1 : c' • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) = c' • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)`. Rewrite `hc'` using `[smul_sub, sub_eq_zero]`. Conclude with `hc'`.

Establish `hsplit : ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) - (d * c) • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]`. Establish `h3 : c' • ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = 0`. Rewrite using `[hsplit, ← h2, smul_sub, smul_comm c' (d * c), h1, smul_comm c' (d * c), sub_self]`. Establish `hb` using `hF4 (fun a => d * y a - d * c * b a) c' hc'0 h3`.

Introduce `a`. Establish `h4 : d * y a - d * c * b a = 0` using `congrFun hb a`. Establish `h5 : y a = c * b a`. Apply `mul_left_cancel₀ hd0` to reduce the goal to its premises. Rewrite using `[← mul_assoc]`.

Conclude with `sub_eq_zero.mp h4`. Establish `hc'' : algebraMap O (FractionRing O) c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc0`. Rewrite using `[Submodule.mem_one]`. Use `⟨b a, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hc''` to reduce the goal to its premises.

Rewrite using `[← map_mul, ← h5, hy a, Algebra.smul_def]`.
-/
theorem c3 : SelmerFInjective := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4
    x m hx

  obtain ⟨⟨c, hc⟩, hcx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin j)) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcx' : ∀ a, ∃ t : O, algebraMap O (FractionRing O) t = c • x a :=
    fun a => RingHom.mem_rangeS.mp (hcx a (Finset.mem_univ a))
  choose y hy using hcx'
  obtain ⟨v, rfl⟩ := hq m
  obtain ⟨d, hd0, hw'⟩ := hsat (c • v)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hw'
  have he0 : d * c ≠ 0 := mul_ne_zero hd0 hc0
  have hK0 : algebraMap O (FractionRing O) (d * c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr he0

  have cancelV : ∀ u u' : V, (d * c) • u = (d * c) • u' → u = u' := by
    intro u u' h
    rw [← algebraMap_smul (FractionRing O) (d * c) u, ← algebraMap_smul (FractionRing O) (d * c) u'] at h
    exact smul_right_injective V hK0 h
  have cancelL : ∀ a b : L, (d * c) • a = (d * c) • b → a = b := by
    intro a b h
    apply hi
    apply cancelV
    have h' := congrArg i h
    rwa [map_smul, map_smul] at h'

  have hf : ∀ g : D, ∃ zg : L, i zg = ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) := by
    intro g
    have hmem : ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_sub, hx g, hqρ]
      exact sub_self _
    rw [hker] at hmem
    exact LinearMap.mem_range.mp hmem
  choose z hz using hf
  obtain ⟨Y, hYdef⟩ : ∃ Y : coZ1s ρL, Y = ∑ a, (d * y a) • κ a - cobZ ρL w := ⟨_, rfl⟩
  have hYg : ∀ g, (Y : D → L) g = ∑ a, (d * y a) • (κ a : D → L) g - (ρL g w - w) := by
    intro g
    rw [hYdef, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  have hY : ∀ g, (d * c) • z g = (Y : D → L) g := by
    intro g
    apply hi
    rw [hYg g, map_smul, hz g, map_sub, map_sub, map_sum, hiρ, hw, smul_sub, smul_sub, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, mul_smul, mul_smul, ← smul_assoc c (x a), ← hy a, algebraMap_smul]
    · rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, mul_smul, mul_smul]

  have hzc : z ∈ coZ1s ρL := by
    show ∀ g h, z (g * h) = z g + ρL g (z h)
    intro g h
    apply cancelL
    rw [smul_add, ← map_smul, hY, hY, hY]
    exact Y.2 g h
  have hZY : (d * c) • (⟨z, hzc⟩ : coZ1s ρL) = Y := Subtype.ext (funext hY)
  have hYcl : (Submodule.mkQ _ Y : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [hYdef, map_sub, mkQ_cobZ, sub_zero, map_sum]
    simp only [map_smul]
  have h2 : (d * c) • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [← map_smul, hZY, hYcl]
  have hZF : (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) ∈ Ff := by
    apply hF1 (d * c) _ he0
    rw [h2]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hF2 a)
  obtain ⟨b, c', hc'0, hc'⟩ := hF3 _ hZF
  have h1 : c' • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      c' • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [smul_sub, sub_eq_zero] at hc'
    exact hc'
  have hsplit : ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) -
        (d * c) • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]
  have h3 : c' • ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 := by
    rw [hsplit, ← h2, smul_sub, smul_comm c' (d * c), h1, smul_comm c' (d * c), sub_self]
  have hb := hF4 (fun a => d * y a - d * c * b a) c' hc'0 h3
  intro a
  have h4 : d * y a - d * c * b a = 0 := congrFun hb a
  have h5 : y a = c * b a := by
    apply mul_left_cancel₀ hd0
    rw [← mul_assoc]
    exact sub_eq_zero.mp h4
  have hc'' : algebraMap O (FractionRing O) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc0
  rw [Submodule.mem_one]
  refine ⟨b a, ?_⟩
  apply mul_left_cancel₀ hc''
  rw [← map_mul, ← h5, hy a, Algebra.smul_def]

end Formalism.RepresentationBoundsCohomology.BR
