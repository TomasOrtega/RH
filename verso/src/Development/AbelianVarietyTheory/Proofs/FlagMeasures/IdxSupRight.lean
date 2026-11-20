import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Compl

section General

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
The claim follows from `DelScale.idx_sup le_rfl`.
-/
theorem idx_sup_right (X B : Submodule R W) : idx (X ⊔ B) B = idx X B :=
  DelScale.idx_sup le_rfl

/- English proof (translation)
Rewrite using `[sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), sup_comm M (U ⊓ _), idx_sup_right, ← DelScale.idx_inf_left, ← DelScale.idx_inf_left _ M]`. Use `congr 1`. Conclude with `le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_left)))`.
-/
theorem idx_glue (M U U' : Submodule R W) :
    idx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), sup_comm M (U ⊓ _), idx_sup_right,
    ← DelScale.idx_inf_left, ← DelScale.idx_inf_left _ M]
  congr 1
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_left)))

/- English proof (translation)
Establish `: idx (M ⊓ U) (U ⊓ (M ⊔ U')) = 1` using `AddSubgroup.relIndex_eq_one.2 fun x hx => ⟨hx.2, Submodule.mem_sup_left hx.1⟩`. Rewrite using `[gidx, this, idx_glue]`. Simplify using the standard rewrite rules.
-/
theorem gidx_glue (M U U' : Submodule R W) :
    gidx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  have : idx (M ⊓ U) (U ⊓ (M ⊔ U')) = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun x hx => ⟨hx.2, Submodule.mem_sup_left hx.1⟩
  rw [gidx, this, idx_glue]
  simp

/- English proof (translation)
Establish `h1 : ∀ x : W, ∃ y : W, x ∈ t → y ∈ U' ∧ x - y ∈ M`. Introduce `x`. Distinguish the cases in `hx : x ∈ t`. Establish `: x ∈ U ⊓ (M ⊔ U')` using `h ▸ Submodule.mem_sup_right (Submodule.subset_span hx)`. Take `⟨m, hm, y, hy, e⟩` from `Submodule.mem_sup.1 this.2`.

Conclude with `⟨y, fun _ => ⟨hy, by rw [← e]; simpa using hm⟩⟩`. Conclude with `⟨0, fun h => absurd h hx⟩`. Use `choose f hf using h1`. Use `⟨t.image f, Finset.card_image_le, ?_⟩` and prove the remaining obligations. Establish `a : Submodule.span R (t.image f : Set W) ≤ U'`.

Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hy)`. Conclude with `(hf x hx).1`. Establish `b : M ⊔ Submodule.span R (t : Set W) = M ⊔ Submodule.span R (t.image f : Set W)`.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup.2 ⟨_, (hf x hx).2, f x, Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), by abel⟩`. Use `sup_le le_sup_left (Submodule.span_le.2 fun y hy => ?_)` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hy)`.

Conclude with `Submodule.mem_sup.2 ⟨_, M.neg_mem (hf x hx).2, x, Submodule.subset_span hx, by abel⟩`. Establish `c : (M ⊔ U) ⊓ (M ⊔ U') = M ⊔ Submodule.span R (t.image f : Set W)`. Rewrite using `[sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), h, ← sup_assoc, sup_inf_self, b]`. Establish `d : U' ⊓ (M ⊔ U) = ((M ⊔ U) ⊓ (M ⊔ U')) ⊓ U'`. Rewrite using `[inf_assoc, inf_comm U', inf_eq_right.2 (le_sup_right : U' ≤ M ⊔ U')]`.

Rewrite using `[d, c, sup_comm M, sup_inf_assoc_of_le M a, sup_comm]`.
-/
theorem gen_glue (M U U' : Submodule R W) (t : Finset W)
    (h : U ⊓ (M ⊔ U') = (M ⊓ U) ⊔ Submodule.span R (t : Set W)) :
    ∃ t' : Finset W, t'.card ≤ t.card ∧ U' ⊓ (M ⊔ U) = (M ⊓ U') ⊔ Submodule.span R (t' : Set W) := by
  have h1 : ∀ x : W, ∃ y : W, x ∈ t → y ∈ U' ∧ x - y ∈ M := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ U ⊓ (M ⊔ U') := h ▸ Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨m, hm, y, hy, e⟩ := Submodule.mem_sup.1 this.2
      exact ⟨y, fun _ => ⟨hy, by rw [← e]; simpa using hm⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  refine ⟨t.image f, Finset.card_image_le, ?_⟩
  have a : Submodule.span R (t.image f : Set W) ≤ U' := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hf x hx).1
  have b : M ⊔ Submodule.span R (t : Set W) = M ⊔ Submodule.span R (t.image f : Set W) := by
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
      exact Submodule.mem_sup.2 ⟨_, (hf x hx).2, f x,
        Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), by abel⟩
    · refine sup_le le_sup_left (Submodule.span_le.2 fun y hy => ?_)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact Submodule.mem_sup.2 ⟨_, M.neg_mem (hf x hx).2, x, Submodule.subset_span hx, by abel⟩
  have c : (M ⊔ U) ⊓ (M ⊔ U') = M ⊔ Submodule.span R (t.image f : Set W) := by
    rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), h, ← sup_assoc, sup_inf_self, b]
  have d : U' ⊓ (M ⊔ U) = ((M ⊔ U) ⊓ (M ⊔ U')) ⊓ U' := by
    rw [inf_assoc, inf_comm U', inf_eq_right.2 (le_sup_right : U' ≤ M ⊔ U')]
  rw [d, c, sup_comm M, sup_inf_assoc_of_le M a, sup_comm]

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
/- English proof (translation)
Take `⟨s, hs⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set V) v hv`. Rewrite `hs` using `[Submodule.span_eq]`. Use `⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_smul]`. Conclude with `hs`.
-/
theorem exists_mult {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ M := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set V) v hv
  rw [Submodule.span_eq] at hs
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs

omit [StarRing K] [FiniteDimensional K V] in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_le.2 fun x hx => hx.2`. Introduce `v hv`. Take `⟨c, hc, h⟩` from `exists_mult (hT hv)`. Rewrite using `[← Submodule.smul_mem_iff _ hc]`.

Conclude with `Submodule.subset_span ⟨h, T.smul_mem c hv⟩`.
-/
theorem span_inf {M : Submodule (𝓞 K) V} {T : Submodule K V} (hT : T ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ rs (𝓞 K) T : Submodule (𝓞 K) V) : Set V) = T := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.2
  · intro v hv
    obtain ⟨c, hc, h⟩ := exists_mult (hT hv)
    rw [← Submodule.smul_mem_iff _ hc]
    exact Submodule.subset_span ⟨h, T.smul_mem c hv⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective I.subtype (Submodule.ker_subtype I)`. Establish `hr' : ∀ x (hx : x ∈ I), (r x : V) = x` using `fun x hx => congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)`. Use `set p : V →ₗ[K] V := LinearMap.id - I.subtype ∘ₗ r with hp`. Establish `hpx : ∀ x, p x = x - r x` using `fun x => rfl`. Use `set C : Submodule K V := S ⊓ LinearMap.ker r with hCd`.

Establish `hCS : C ≤ S` using `inf_le_left`. Establish `hpC : ∀ x ∈ S, p x ∈ C` using `fun x hx => ⟨S.sub_mem hx (hIS (r x).2), by`. Express the relevant statement in the definitionally equal form `r (p x) = 0`. Rewrite using `[hpx, map_sub, sub_eq_zero]`. Conclude with `(Subtype.ext (hr' _ (r x).2)).symm⟩`.

Establish `hpI : ∀ x, x - p x ∈ I` using `fun x => by rw [hpx]; simp`. Establish `hI : ∀ x ∈ I, p x = 0` using `fun x hx => by rw [hpx, hr' x hx, sub_self]`. Establish `hC : ∀ x ∈ C, p x = x` using `fun x hx => by`. Establish `: r x = 0` using `hx.2`. Rewrite using `[hpx, this]`.

Simplify using the standard rewrite rules. Establish `o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0` using `fun i hi => (hrad i (hIS hi)).2 hi`. Establish `o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0` using `fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]`. Establish `o3 : ∀ y ∈ S, ∀ x, H.B y (p x) = H.B y x` using `fun y hy x => by`. Rewrite using `[hpx, map_sub, o2 _ (r x).2 y hy, sub_zero]`.

Establish `o4 : ∀ y ∈ S, ∀ x, H.B (p x) y = H.B x y` using `fun y hy x => by`. Rewrite using `[← H.herm, o3 y hy, H.herm]`. Establish `hpT : ∀ x ∈ T, p x ∈ T` using `fun x hx => T.sub_mem hx (hIT (r x).2)`. Set `HC : HermSpace K C` to `{ B := H.B.domRestrict₁₂ C C herm := fun x y => H.herm x y nondeg := fun x hx => by`. Establish `: (x : V) ∈ I` using `(hrad x (hCS x.2)).1 fun y hy => by`.

Rewrite using `[← o3 x (hCS x.2)]`. Conclude with `hx ⟨_, hpC y hy⟩`. Conclude with `Subtype.ext ((hC x x.2).symm.trans (hI x this)) }`. Establish `hB : ∀ x y : C, HC.B x y = H.B x y` using `fun _ _ => rfl`. Take `⟨a, b⟩` from `DelScale.le_of_latMod hM.1`.

Establish `hpM : ∀ x ∈ M, p x ∈ M` using `fun x hx => M.sub_mem hx (a (r x).2)`. Establish `L` using `DelScale.latIn_isLattice p hCS hpC hpI hI hC hM.1`. Establish `hMd : ∀ y, y ∈ M ↔ y ∈ S ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule (𝓞 K) K)` using `fun y => by`. Rewrite using `[← hM.1.2, ← mem_dual_iff, hM.2]`. Establish `hU : IsUnimod HC (GlobalTheory.Mass.latIn C M)`.

Use `⟨(isLatMod_top_bot_iff _).2 L, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[mem_dual_iff, L.span_eq_top]`. Express the relevant statement in the definitionally equal form `_ ↔ (y : V) ∈ M`. Rewrite using `[hMd]`.

Use `⟨fun hy => ⟨hCS y.2, fun x hx => ?_⟩, fun hy => ⟨trivial, fun x hx => hy.2 x hx⟩⟩` and prove the remaining obligations. Rewrite using `[← o3 y (hCS y.2)]`. Conclude with `hy.2 ⟨p x, hpC x (b hx)⟩ (hpM x hx)`. Prove the components needed by the constructor for the conclusion. Use extensionality with `d`.

Rewrite using `[mem_dual_iff, span_inf (hM.1.2 ▸ hTS)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, hdM⟩`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `hx : ∀ x : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)), IsIntegral ℤ (H.B ((x : C) : V) d)`.

Introduce `x`. Rewrite using `[← UnimodQuot.mem_one_iff, ← H.herm]`. Conclude with `UnimodQuot.star_mem_one (hdM _ ⟨x.2.1, x.2.2⟩)`. Set `φ : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)) →ₗ[𝓞 K] 𝓞 K` to `{ toFun := fun x => ⟨H.B ((x : C) : V) d, hx x⟩ map_add' := fun a b => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `show H.B (((a : C) : V) + (b : C)) d = H.B (a : C) d + H.B (b : C) d`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun a b => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show H.B (a • ((b : C) : V)) d = algebraMap (𝓞 K) K a * H.B (b : C) d`.

Rewrite using `[← algebraMap_smul K a, map_smul]`. Use `rfl }`. Take `⟨y, hy, h'⟩` from `UnimodQuot.exists_lattice_rep HC hU (T.comap C.subtype) φ`. Use `Submodule.mem_sup.2 ⟨y, hy, d - y, ⟨S.sub_mem (hTS hd) (hCS y.2), ?_⟩, by abel⟩` and prove the remaining obligations. Use `(mem_perp_iff H T _).2 fun x hx => ?_` and prove the remaining obligations.

Take `⟨c, hc, h⟩` from `exists_mult (M := M) (v := x) (hM.1.2 ▸ hTS hx)`. Establish `hcT` using `T.smul_mem c hx`. Establish `h1 : H.B (p (c • x)) y = H.B (p (c • x)) d` using `h' ⟨⟨p (c • x), hpC _ (hTS hcT)⟩, hpM _ h, hpT _ hcT⟩`. Rewrite `h1` using `[o4 _ (hCS y.2), o4 _ (hTS hd), map_smul, LinearMap.smul_apply, LinearMap.smul_apply]`. Rewrite using `[← H.herm, map_sub, smul_right_injective K hc h1, sub_self, star_zero]`.

Introduce and unpack `⟨hd, hdM⟩`. Use `⟨hd, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, u, hu, rfl⟩` from `Submodule.mem_sup.1 hdM`. Rewrite using `[map_add, LinearMap.add_apply, (mem_perp_iff H T u).1 hu.2 x hx.2, add_zero]`. Conclude with `((hMd m).1 hm).2 x hx.1`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `s ⟨hs, hs'⟩`. Establish `h1 : (⟨p s, hpC s hs⟩ : C) ∈ T.comap C.subtype`. Apply `UnimodQuot.mem_of_perp_perp HC` to reduce the goal to its premises. Introduce `x hx`.

Rewrite using `[hB]`. Express the relevant statement in the definitionally equal form `H.B x (p s) = 0`. Rewrite using `[o3 _ (hCS x.2), ← H.herm, (mem_perp_iff H _ s).1 hs' x ⟨hCS x.2, ?_⟩, star_zero]`. Use `(mem_perp_iff H T _).2 fun z hz => ?_` and prove the remaining obligations. Rewrite using `[← o3 _ (hCS x.2)]`.

Conclude with `(mem_perp_iff HC _ x).1 hx ⟨p z, hpC z (hTS hz)⟩ (hpT z hz)`. Establish `h2 : p s ∈ T` using `h1`. Simplify using `using T.add_mem h2 (hIT (hpI s))`. Introduce `x hx`. Use `⟨hTS hx, (mem_perp_iff H _ _).2 fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[← H.herm, (mem_perp_iff H T y).1 hy.2 x hx, star_zero]`.
-/
theorem key (H : HermSpace K V) {M : Submodule (𝓞 K) V} {S I : Submodule K V} (hIS : I ≤ S)
    (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {T : Submodule K V} (hIT : I ≤ T) (hTS : T ≤ S) :
    dual H (M ⊓ rs (𝓞 K) T) = rs (𝓞 K) T ⊓ (M ⊔ rs (𝓞 K) (S ⊓ perp H T)) ∧
      S ⊓ perp H (S ⊓ perp H T) = T := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective I.subtype (Submodule.ker_subtype I)
  have hr' : ∀ x (hx : x ∈ I), (r x : V) = x := fun x hx =>
    congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  set p : V →ₗ[K] V := LinearMap.id - I.subtype ∘ₗ r with hp
  have hpx : ∀ x, p x = x - r x := fun x => rfl
  set C : Submodule K V := S ⊓ LinearMap.ker r with hCd
  have hCS : C ≤ S := inf_le_left
  have hpC : ∀ x ∈ S, p x ∈ C := fun x hx => ⟨S.sub_mem hx (hIS (r x).2), by
    change r (p x) = 0
    rw [hpx, map_sub, sub_eq_zero]
    exact (Subtype.ext (hr' _ (r x).2)).symm⟩
  have hpI : ∀ x, x - p x ∈ I := fun x => by rw [hpx]; simp
  have hI : ∀ x ∈ I, p x = 0 := fun x hx => by rw [hpx, hr' x hx, sub_self]
  have hC : ∀ x ∈ C, p x = x := fun x hx => by
    have : r x = 0 := hx.2
    rw [hpx, this]; simp
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have o3 : ∀ y ∈ S, ∀ x, H.B y (p x) = H.B y x := fun y hy x => by
    rw [hpx, map_sub, o2 _ (r x).2 y hy, sub_zero]
  have o4 : ∀ y ∈ S, ∀ x, H.B (p x) y = H.B x y := fun y hy x => by
    rw [← H.herm, o3 y hy, H.herm]
  have hpT : ∀ x ∈ T, p x ∈ T := fun x hx => T.sub_mem hx (hIT (r x).2)
  let HC : HermSpace K C :=
    { B := H.B.domRestrict₁₂ C C
      herm := fun x y => H.herm x y
      nondeg := fun x hx => by
        have : (x : V) ∈ I := (hrad x (hCS x.2)).1 fun y hy => by
          rw [← o3 x (hCS x.2)]; exact hx ⟨_, hpC y hy⟩
        exact Subtype.ext ((hC x x.2).symm.trans (hI x this)) }
  have hB : ∀ x y : C, HC.B x y = H.B x y := fun _ _ => rfl
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hpM : ∀ x ∈ M, p x ∈ M := fun x hx => M.sub_mem hx (a (r x).2)
  have L := DelScale.latIn_isLattice p hCS hpC hpI hI hC hM.1
  have hMd : ∀ y, y ∈ M ↔ y ∈ S ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule (𝓞 K) K) := fun y => by
    rw [← hM.1.2, ← mem_dual_iff, hM.2]
  have hU : IsUnimod HC (GlobalTheory.Mass.latIn C M) := by
    refine ⟨(isLatMod_top_bot_iff _).2 L, ?_⟩
    ext y
    rw [mem_dual_iff, L.span_eq_top]
    change _ ↔ (y : V) ∈ M
    rw [hMd]
    refine ⟨fun hy => ⟨hCS y.2, fun x hx => ?_⟩, fun hy => ⟨trivial, fun x hx => hy.2 x hx⟩⟩
    rw [← o3 y (hCS y.2)]
    exact hy.2 ⟨p x, hpC x (b hx)⟩ (hpM x hx)
  constructor
  · ext d
    rw [mem_dual_iff, span_inf (hM.1.2 ▸ hTS)]
    constructor
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, ?_⟩
      have hx : ∀ x : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)),
          IsIntegral ℤ (H.B ((x : C) : V) d) := by
        intro x
        rw [← UnimodQuot.mem_one_iff, ← H.herm]
        exact UnimodQuot.star_mem_one (hdM _ ⟨x.2.1, x.2.2⟩)
      let φ : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)) →ₗ[𝓞 K] 𝓞 K :=
        { toFun := fun x => ⟨H.B ((x : C) : V) d, hx x⟩
          map_add' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (((a : C) : V) + (b : C)) d = H.B (a : C) d + H.B (b : C) d
            simp
          map_smul' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (a • ((b : C) : V)) d = algebraMap (𝓞 K) K a * H.B (b : C) d
            rw [← algebraMap_smul K a, map_smul]
            rfl }
      obtain ⟨y, hy, h'⟩ := UnimodQuot.exists_lattice_rep HC hU (T.comap C.subtype) φ
      refine Submodule.mem_sup.2 ⟨y, hy, d - y, ⟨S.sub_mem (hTS hd) (hCS y.2), ?_⟩, by abel⟩
      refine (mem_perp_iff H T _).2 fun x hx => ?_
      obtain ⟨c, hc, h⟩ := exists_mult (M := M) (v := x) (hM.1.2 ▸ hTS hx)
      have hcT := T.smul_mem c hx
      have h1 : H.B (p (c • x)) y = H.B (p (c • x)) d :=
        h' ⟨⟨p (c • x), hpC _ (hTS hcT)⟩, hpM _ h, hpT _ hcT⟩
      rw [o4 _ (hCS y.2), o4 _ (hTS hd), map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [← H.herm, map_sub, smul_right_injective K hc h1, sub_self, star_zero]
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, fun x hx => ?_⟩
      obtain ⟨m, hm, u, hu, rfl⟩ := Submodule.mem_sup.1 hdM
      rw [map_add, LinearMap.add_apply, (mem_perp_iff H T u).1 hu.2 x hx.2, add_zero]
      exact ((hMd m).1 hm).2 x hx.1
  · apply le_antisymm
    · rintro s ⟨hs, hs'⟩
      have h1 : (⟨p s, hpC s hs⟩ : C) ∈ T.comap C.subtype := by
        apply UnimodQuot.mem_of_perp_perp HC
        intro x hx
        rw [hB]
        change H.B x (p s) = 0
        rw [o3 _ (hCS x.2), ← H.herm, (mem_perp_iff H _ s).1 hs' x ⟨hCS x.2, ?_⟩, star_zero]
        refine (mem_perp_iff H T _).2 fun z hz => ?_
        rw [← o3 _ (hCS x.2)]
        exact (mem_perp_iff HC _ x).1 hx ⟨p z, hpC z (hTS hz)⟩ (hpT z hz)
      have h2 : p s ∈ T := h1
      simpa using T.add_mem h2 (hIT (hpI s))
    · intro x hx
      refine ⟨hTS hx, (mem_perp_iff H _ _).2 fun y hy => ?_⟩
      rw [← H.herm, (mem_perp_iff H T y).1 hy.2 x hx, star_zero]

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H _ M S I U hIU hUS hrad _ hM`. Establish `hIS` using `hIU.trans hUS`. Take `⟨h1, h2⟩` from `key H hIS hrad hM hIU hUS`. Establish `hI' : I ≤ S ⊓ perp H U` using `fun i hi => ⟨hIS hi, (mem_perp_iff H U i).2 fun x hx => (hrad i (hIS hi)).2 hi x (hUS hx)⟩`. Take `⟨h3, -⟩` from `key H hIS hrad hM hI' inf_le_left`.

Rewrite `h3` using `[h2]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[del, del, h1, h3, gidx_glue, gidx_glue, inf_comm]`. Introduce and unpack `e ⟨t, ht, h⟩`. Rewrite `h` using `[h1]`.

Take `⟨t', ht', h'⟩` from `gen_glue _ _ _ t h`. Conclude with `⟨t', ht'.trans ht, h3.trans h'⟩`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (M : Submodule (𝓞 K) V) (S I U : Submodule K V), I ≤ U → U ≤ S → (∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) → (∀ x ∈ U, (∀ y ∈ U, H.B x y = 0) ↔ x ∈ I) → IsUnimodMod H M S I → del H (M ⊓ rs (𝓞 K) U) = del H (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) ∧ ∀ e : ℕ, GenBy (dual H (M ⊓ rs (𝓞 K) U)) (M ⊓ rs (𝓞 K) U) e → GenBy (dual H (M ⊓ rs (𝓞 K) (S ⊓ perp H U))) (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) e := by
  intro K V _ _ _ _ _ _ _ _ H _ M S I U hIU hUS hrad _ hM
  have hIS := hIU.trans hUS
  obtain ⟨h1, h2⟩ := key H hIS hrad hM hIU hUS
  have hI' : I ≤ S ⊓ perp H U := fun i hi =>
    ⟨hIS hi, (mem_perp_iff H U i).2 fun x hx => (hrad i (hIS hi)).2 hi x (hUS hx)⟩
  obtain ⟨h3, -⟩ := key H hIS hrad hM hI' inf_le_left
  rw [h2] at h3
  constructor
  · rw [del, del, h1, h3, gidx_glue, gidx_glue, inf_comm]
  · rintro e ⟨t, ht, h⟩
    rw [h1] at h
    obtain ⟨t', ht', h'⟩ := gen_glue _ _ _ t h
    exact ⟨t', ht'.trans ht, h3.trans h'⟩

end GlobalTheory.DegCnt.Compl
