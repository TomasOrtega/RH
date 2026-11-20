import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFixedOfFinset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult CompanionTheory.Rg.Fl
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RestT

/- English proof (translation)
Take `⟨x, hx, hxK⟩` from `exists_fixed_ne_zero hi hδ hρ K hw hK`. Establish `hn : (‖x‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hx`. Establish `h1 : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1` using `by simp [norm_smul, hx]`. Establish `h2 : ∀ k ∈ K, δ k ((‖x‖ : ℂ)⁻¹ • x) = (‖x‖ : ℂ)⁻¹ • x` using `fun k hk => by rw [map_smul, hxK k hk]`. Use `⟨_, h1, h2, fun h hh => hA.apply_fixed hi hδ hρ K h1 (fun y hy => ?_) hh⟩` and prove the remaining obligations.

Establish `h3 : (‖x‖ : ℂ)⁻¹ • x ≠ 0` using `fun e => by simp [e] at h1`. Conclude with `hl _ h3 h2 y hy`.
-/
theorem exists_good {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}
    {A : X → X → (H →L[ℂ] H)} (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ)
    (K : Subgroup G) (hl : ∀ x : X, x ≠ 0 → (∀ k ∈ K, δ k x = x) → ∀ y, (∀ k ∈ K, δ k y = y) → ∃ c : ℂ, y = c • x)
    {w : H} (hw : w ≠ 0) (hK : ∀ k ∈ K, ρ k w = w) :
    ∃ ξ : X, ‖ξ‖ = 1 ∧ (∀ k ∈ K, δ k ξ = ξ) ∧ ∀ h : H, (∀ k ∈ K, ρ k h = h) → A ξ ξ h = h := by
  obtain ⟨x, hx, hxK⟩ := exists_fixed_ne_zero hi hδ hρ K hw hK
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
  have h1 : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by simp [norm_smul, hx]
  have h2 : ∀ k ∈ K, δ k ((‖x‖ : ℂ)⁻¹ • x) = (‖x‖ : ℂ)⁻¹ • x := fun k hk => by rw [map_smul, hxK k hk]
  refine ⟨_, h1, h2, fun h hh => hA.apply_fixed hi hδ hρ K h1 (fun y hy => ?_) hh⟩
  have h3 : (‖x‖ : ℂ)⁻¹ • x ≠ 0 := fun e => by simp [e] at h1
  exact hl _ h3 h2 y hy

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
The claim follows from `GAd_ext σ J (fun w => h (.inl w)) fun v => h (.inr v)`.
-/
theorem ext_projPl {a b : GAd σ J} (h : ∀ u, projPl σ J u a = projPl σ J u b) : a = b :=
  GAd_ext σ J (fun w => h (.inl w)) fun v => h (.inr v)

/- English proof (translation)
Use `ext_projPl fun u => ?_` and prove the remaining obligations. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Simplify using `[h]`. Simplify using `[projPl_embPl_ne σ J e]`.
-/
theorem commute_embPl {v : Formalism.MainNotions.SchurIrreducible.Pl F} {g : GAd σ J} (h : projPl σ J v g = 1) (x : GPl σ J v) :
    Commute g (embPl σ J v x) := by
  refine ext_projPl fun u => ?_
  by_cases e : u = v
  · subst e
    simp [h]
  · simp [projPl_embPl_ne σ J e]

/- English proof (translation)
Use `haveI := hπ.complete`. Use `haveI := hπ.irred.1`. Use `haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J`. Take `⟨U, w, hU, hw, hfix⟩` from `hFix (GFin σ J) H (π.comp (ofFin σ J)) (fun g v => hπ.unitary.norm_apply _ _) (fun v => (hπ.unitary.continuous_apply v).comp (continuous_ofFin σ J))`. Take `⟨S, hS⟩` from `GlobalTheory.PlaceGen.exists_levelOff_le σ J L (U.comap (projFin σ J)) (hU.preimage (continuous_projFin σ J))`.

Use `⟨S, w, hw, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hr : k ∈ (ofFin σ J).range`. Rewrite using `[range_ofFin]`. Conclude with `(mem_levelOff.1 hk).1`. Take `⟨g, rfl⟩` from `hr`.

Use `hS hk` as an intermediate fact. Simplify using `only [Subgroup.mem_comap, projFin_ofFin] at this`. Conclude with `hfix g this`.
-/
theorem exists_levelOff_fixed (hFix : StFixVec) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : GAd σ J →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (w : H), w ≠ 0 ∧ ∀ k ∈ levelOff σ J L S, π k w = w := by
  haveI := hπ.complete
  haveI := hπ.irred.1
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  obtain ⟨U, w, hU, hw, hfix⟩ := hFix (GFin σ J) H (π.comp (ofFin σ J)) (fun g v => hπ.unitary.norm_apply _ _)
    (fun v => (hπ.unitary.continuous_apply v).comp (continuous_ofFin σ J))
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le σ J L (U.comap (projFin σ J)) (hU.preimage (continuous_projFin σ J))
  refine ⟨S, w, hw, fun k hk => ?_⟩
  have hr : k ∈ (ofFin σ J).range := by
    rw [range_ofFin]
    exact (mem_levelOff.1 hk).1
  obtain ⟨g, rfl⟩ := hr
  have := hS hk
  simp only [Subgroup.mem_comap, projFin_ofFin] at this
  exact hfix g this

/- English proof (translation)
Use `filter_upwards [GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hθ X _ _ δ hδ x hx0 hx y hy`. Take `⟨θ, hθ1, hθ2, hθ3⟩` from `hθ`. Use `haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v`. Establish `hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v))` using `isOpen_stabLoc σ J L v`. Establish `hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v))` using `isCompact_stabLoc σ J L v`.

Establish `hirr` using `GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) X δ hδ (fun K hK hK' => hAdm F E σ hc n J hJ v X δ hδ K hK hK')`. Establish `sm : ∀ z, (∀ k ∈ stabLoc σ J L v, δ k z = z) → z ∈ GlobalTheory.PRep.smoothPart (toRep δ)`. Introduce `z hz`. Set `S : Subgroup (GLoc σ J v)` to `{ carrier := {g | toRep δ g z = z} mul_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Establish `hle : stabLoc σ J L v ≤ S` using `fun k hk => hz k hk`.

Conclude with `Subgroup.isOpen_mono hle hKo`. Set `x' : GlobalTheory.PRep.smoothPart (toRep δ)` to `⟨x, sm x hx⟩`. Establish `hx' : x' ∈ fixed (smRep δ) (stabLoc σ J L v)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hx k hk)`. Establish `hx0' : x' ≠ 0` using `fun e => hx0 (congrArg Subtype.val e)`. Establish `hline` using `GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _ (smRep δ) hirr.1 hirr.2 x' hx' hx0'`.

Establish `hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep δ)) ∈ fixed (smRep δ) (stabLoc σ J L v)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hy k hk)`. Rewrite `hy'` using `[hline]`. Take `⟨c, hc'⟩` from `Submodule.mem_span_singleton.1 hy'`. Conclude with `⟨c, (congrArg Subtype.val hc').symm⟩`.
-/
theorem eventually_line (hAdm : GlobalTheory.Published.UnitaryIrreducibleAdmissible) (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsLattice E L] :
    ∀ᶠ v in cofinite, ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      (δ : GLoc σ J v →* (X →L[ℂ] X)), IsIrrUnitary δ → ∀ x : X, x ≠ 0 → (∀ k ∈ stabLoc σ J L v, δ k x = x) →
        ∀ y, (∀ k ∈ stabLoc σ J L v, δ k y = y) → ∃ c : ℂ, y = c • x := by
  filter_upwards [GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hθ X _ _ δ hδ x hx0 hx y hy
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have hirr := GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) X δ hδ
    (fun K hK hK' => hAdm F E σ hc n J hJ v X δ hδ K hK hK')
  have sm : ∀ z, (∀ k ∈ stabLoc σ J L v, δ k z = z) → z ∈ GlobalTheory.PRep.smoothPart (toRep δ) := by
    intro z hz
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep δ g z = z}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => hz k hk
    exact Subgroup.isOpen_mono hle hKo
  let x' : GlobalTheory.PRep.smoothPart (toRep δ) := ⟨x, sm x hx⟩
  have hx' : x' ∈ fixed (smRep δ) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hx k hk)
  have hx0' : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hline := GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep δ) hirr.1 hirr.2 x' hx' hx0'
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep δ)) ∈ fixed (smRep δ) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 hy'
  exact ⟨c, (congrArg Subtype.val hc').symm⟩

def plK (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    ∀ u : Formalism.MainNotions.SchurIrreducible.Pl F, Subgroup (GPl σ J u)
  | .inl _ => ⊥
  | .inr v => stabLoc σ J L v

/- English proof (translation)
Establish `hf` using `Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)`. Use `⟨Finset.univ.image Sum.inl ∪ hf.toFinset.image Sum.inr, fun u hu => ?_⟩` and prove the remaining obligations. Break down `u with w | v` into its components or cases. Conclude with `absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))) hu`. Assume the negation of the conclusion as `hn`.

Conclude with `hu (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hn)))`.
-/
theorem exists_finset_projPl_mem (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (g : GAd σ J) :
    ∃ t : Finset (Formalism.MainNotions.SchurIrreducible.Pl F), ∀ u ∉ t, projPl σ J u g ∈ plK σ J L u := by
  classical
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  refine ⟨Finset.univ.image Sum.inl ∪ hf.toFinset.image Sum.inr, fun u hu => ?_⟩
  rcases u with w | v
  · exact absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))) hu
  · by_contra hn
    exact hu (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hn)))

/- English proof (translation)
Break down `u with w | v` into its components or cases. Conclude with `mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 w`. Conclude with `(mem_levelOff.1 hk).2.1 v (hu v rfl)`.
-/
theorem projPl_eq_one_of_mem_levelOff {L : Submodule (𝓞 E) (Fin n → E)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : GAd σ J} (hk : k ∈ levelOff σ J L S) {u : Formalism.MainNotions.SchurIrreducible.Pl F}
    (hu : ∀ v, u = .inr v → v ∈ S) : projPl σ J u k = 1 := by
  rcases u with w | v
  · exact mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 w
  · exact (mem_levelOff.1 hk).2.1 v (hu v rfl)

/- English proof (translation)
Use `mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => projArch_emb σ J w v k, fun u hu => ?_, fun u _ => ?_⟩` and prove the remaining obligations. Conclude with `proj_emb_ne σ J (by rintro rfl; exact hv hu) k`. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Simplify using `using hk`.

Rewrite using `[proj_emb_ne σ J e]`. Conclude with `one_mem _`.
-/
theorem embPl_mem_levelOff {L : Submodule (𝓞 E) (Fin n → E)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {k : GLoc σ J v} (hk : k ∈ stabLoc σ J L v) :
    emb σ J v k ∈ levelOff σ J L S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => projArch_emb σ J w v k, fun u hu => ?_, fun u _ => ?_⟩
  · exact proj_emb_ne σ J (by rintro rfl; exact hv hu) k
  · by_cases e : u = v
    · subst e
      simpa using hk
    · rw [proj_emb_ne σ J e]
      exact one_mem _

end Adelic

/- English proof (translation)
Introduce `hOp hFix hAdm F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ R hR`. Use `haveI := hπ.complete`. Use `haveI hL : Submodule.IsLattice E (stdLattice E n) := isLattice_stdLattice`. Use `set L := stdLattice E n with hLdef`. Set `ρ : ∀ v, GPl σ J v →* (H →L[ℂ] H)` to `fun v => π.comp (embPl σ J v)`.

Establish `hρ : ∀ v, IsUnitaryRep (ρ v)` using `fun v => isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)`. Establish `hA'` using `fun v => hOp (GPl σ J v) (R v).H H (R v).π (ρ v) (R v).isIrr (hρ v) (hR v)`. Use `choose A hA0 using hA'`. Establish `hA : ∀ v, IsOpFam (R v).π (ρ v) (A v)` using `hA0`. Establish `hi : ∀ v, IsIsotypic (R v).π (ρ v)` using `hR`.

Establish `hcommπ : ∀ v g, projPl σ J v g = 1 → ∀ y ξ, Commute (π g) (A v y ξ)` using `fun v g h y ξ => ((hA v).commute (hi v) (C := π g) (fun x => (commute_embPl h x).map π) y ξ).symm`. Establish `hAA : ∀ u v, u ≠ v → ∀ y ξ y' ξ', Commute (A u y ξ) (A v y' ξ')` using `fun u v huv y ξ y' ξ' => (hA u).commute (hi u) (C := A v y' ξ') (fun x => (hcommπ v (embPl σ J u x) (projPl_embPl_ne σ J huv.symm x) y' ξ').symm) y ξ`. Take `⟨S, w₀, hw₀, hfix₀⟩` from `exists_levelOff_fixed (σ := σ) (J := J) hFix L hπ`. Establish `hbad` using `Filter.eventually_cofinite.1 (eventually_line hAdm hc hJ L)`. Use `set S₁ := S ∪ hbad.toFinset with hS₁`.

Use `set s : Finset (Formalism.MainNotions.SchurIrreducible.Pl F) := Finset.univ.image Sum.inl ∪ S₁.image Sum.inr with hs`. Establish `hinl : ∀ w, (Sum.inl w : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s` using `fun w => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))`. Establish `hinr : ∀ v, v ∈ S₁ → (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s` using `fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)`. Establish `hmems : ∀ u ∈ s, ∀ v, u = .inr v → v ∈ S₁` using `fun u hu v e => by`. Substitute `e` using the available equality.

Break down `Finset.mem_union.1 hu with h | h` into its components or cases. Take `⟨w, -, hw⟩` from `Finset.mem_image.1 h`. Conclude with `absurd hw (by simp)`. Take `⟨v', hv', e⟩` from `Finset.mem_image.1 h`. Conclude with `Sum.inr_injective e ▸ hv'`.

Establish `hoff : levelOff σ J L S₁ ≤ levelOff σ J L S` using `GlobalTheory.PlaceGen.levelOff_anti σ J L Finset.subset_union_left`. Establish `hKlev : ∀ u, u ∉ s → ∀ k ∈ plK σ J L u, embPl σ J u k ∈ levelOff σ J L S₁` using `fun u hu k hk => by`. Break down `u with w | v` into its components or cases. Conclude with `absurd (hinl w) hu`. Conclude with `embPl_mem_levelOff (fun h => hu (hinr v h)) hk`.

Establish `hgood : ∀ u, ∃ ξ : (R u).H, u ∉ s → ‖ξ‖ = 1 ∧ (∀ k ∈ plK σ J L u, (R u).π k ξ = ξ) ∧ ∀ h : H, (∀ k ∈ plK σ J L u, ρ u k h = h) → A u ξ ξ h = h` using `fun u => by`. Distinguish the cases in `hu : u ∈ s`. Conclude with `⟨0, fun h => absurd hu h⟩`. Break down `u with w | v` into its components or cases. Conclude with `absurd (hinl w) hu`.

Establish `hv : v ∉ hbad.toFinset` using `fun h => hu (hinr v (Finset.mem_union_right _ h))`. Establish `hl : ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (δ : GLoc σ J v →* (X →L[ℂ] X)), IsIrrUnitary δ → ∀ x : X, x ≠ 0 → (∀ k ∈ stabLoc σ J L v, δ k x = x) → ∀ y, (∀ k ∈ stabLoc σ J L v, δ k y = y) → ∃ c : ℂ, y = c • x`. Assume the negation of the conclusion as `hn`. Conclude with `hv (hbad.mem_toFinset.2 hn)`. Take `⟨ξ, h1, h2, h3⟩` from `exists_good (hA (.inr v)) (hi (.inr v)) (R (.inr v)).isIrr (hρ (.inr v)) (plK σ J L (.inr v)) (hl _ _ (R (.inr v)).isIrr) hw₀ (fun k hk => hfix₀ _ (hoff (hKlev _ hu k hk)))`.

Conclude with `⟨ξ, fun _ => ⟨h1, h2, h3⟩⟩`. Use `choose ξg hξg using hgood`. Set `Inv : H → Prop` to `fun w => (∀ k ∈ levelOff σ J L S₁, π k w = w) ∧ ∀ u, u ∉ s → A u (ξg u) (ξg u) w = w`. Establish `hproj : ∀ i (ξ : (R i).H), ‖ξ‖ = 1 → A i ξ ξ * A i ξ ξ = A i ξ ξ` using `fun i ξ h => by`. Rewrite using `[(hA i).mul (hi i), inner_self_eq_norm_sq_to_K, h]`.

Simplify using the standard rewrite rules. Take `⟨ξs, w₁, hw₁, hI, hξs⟩` from `exists_fixed_of_finset (A := A) hAA (fun i w hw => (hA i).exists_ne_zero (hi i) (R i).isIrr (hρ i) hw) hproj Inv s (fun i his ξ w hw => ⟨fun k hk => by`. Establish `hc1` using `(hcommπ i k (projPl_eq_one_of_mem_levelOff hk (hmems i his)) ξ ξ).eq`. Use `DFunLike.congr_fun hc1 w` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`.

Rewrite using `[this, hw.1 k hk],`. Use `fun u hu => by`. Establish `hne : u ≠ i` using `fun e => hu (e ▸ his)`. Use `DFunLike.congr_fun (hAA u i hne (ξg u) (ξg u) ξ ξ).eq w` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`.

Rewrite using `[this, hw.2 u hu]⟩)`. Use the proof step `(w₀ := w₀) ⟨fun k hk => hfix₀ k (hoff hk), fun u hu => (hξg u hu).2.2 w₀ fun k hk => hfix₀ _ (hoff (hKlev u hu k hk))⟩ hw₀`. Set `ξ : ∀ u, (R u).H` to `fun u => if u ∈ s then ξs u else ξg u`. Establish `hξ : ∀ u, ‖ξ u‖ = 1` using `fun u => by`. Distinguish the cases in `hu : u ∈ s`.

Simplify using `only [ξ, if_pos hu]`. Conclude with `(hξs u hu).1`. Simplify using `only [ξ, if_neg hu]`. Conclude with `(hξg u hu).1`. Establish `hfixall : ∀ u, A u (ξ u) (ξ u) w₁ = w₁` using `fun u => by`.

Distinguish the cases in `hu : u ∈ s`. Simplify using `only [ξ, if_pos hu]`. Conclude with `(hξs u hu).2`. Simplify using `only [ξ, if_neg hu]`. Conclude with `hI.2 u hu`.

Establish `hn : (‖w₁‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hw₁`. Use `set w := (‖w₁‖ : ℂ)⁻¹ • w₁ with hwdef`. Establish `hw1 : ‖w‖ = 1` using `by simp [hwdef, norm_smul, hw₁]`. Establish `hlev : ∀ k ∈ levelOff σ J L S₁, π k w = w` using `fun k hk => by`. Rewrite using `[hwdef, map_smul, hI.1 k hk]`.

Set `a : ∀ u, (R u).H → (H →L[ℂ] H)` to `fun u y => A u y (ξ u)`. Establish `hac : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y')` using `fun i j h y y' => hAA i j h _ _ _ _`. Take `⟨B, hB⟩` from `exists_isRestrTensor (a := a) (ξ := ξ) (w := w) (p := projPl σ J) (e := embPl σ J) (δ := fun v => (R v).π) (π := π) hac hπ.irred hξ hw1 (fun i => by simp only [a, hwdef, map_smul, hfixall i]) (fun i y y' => by`. Simplify using `only [a]`. Rewrite using `[(hA i).adjoint_eq (hi i) (R i).isIrr (hρ i), (hA i).mul (hi i)])`.

Use the proof step `(fun i x => projPl_embPl_self σ J i x) (fun i j h x => projPl_embPl_ne σ J h.symm x)`. Use the proof step `(fun v g h y => hcommπ v g h y _)`. Use the proof step `(fun i x y => (hA i).rep_mul (hi i) x y (ξ i))`. Use the proof step `(fun g => by`. Take `⟨t, ht⟩` from `exists_finset_projPl_mem (σ := σ) (J := J) L g`.

Use `⟨s ∪ t, fun i hi' => ?_, fun s' hs' k hk1 hk2 => hlev k ?_⟩` and prove the remaining obligations. Establish `h1 : i ∉ s` using `fun h => hi' (Finset.mem_union_left _ h)`. Establish `h2 : i ∉ t` using `fun h => hi' (Finset.mem_union_right _ h)`. Simplify using `only [ξ, if_neg h1]`. Conclude with `(hξg i h1).2.1 _ (ht i h2)`.

Use `mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => hk1 _ (hs' (Finset.mem_union_left _ (hinl w))), fun v hv => hk1 _ (hs' (Finset.mem_union_left _ (hinr v hv))), fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s'`. Establish `: projPl σ J (.inr v) k = 1` using `hk1 _ h`. Express the relevant statement in the definitionally equal form `projPl σ J (.inr v) k ∈ stabLoc σ J L v`. Rewrite using `[this]`.

Conclude with `one_mem _`. Establish `h3 : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∉ t` using `fun h' => h (hs' (Finset.mem_union_right _ h'))`. Express the relevant statement in the definitionally equal form `projPl σ J (.inr v) k ∈ stabLoc σ J L v`. Rewrite using `[hk2 _ h]`. Conclude with `ht _ h3)`.

Conclude with `⟨ξ, B, hB⟩`.
-/
theorem stTensor : StTensor := by
  intro hOp hFix hAdm F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ R hR
  classical
  haveI := hπ.complete
  haveI hL : Submodule.IsLattice E (stdLattice E n) := isLattice_stdLattice
  set L := stdLattice E n with hLdef
  let ρ : ∀ v, GPl σ J v →* (H →L[ℂ] H) := fun v => π.comp (embPl σ J v)
  have hρ : ∀ v, IsUnitaryRep (ρ v) := fun v => isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)
  have hA' := fun v => hOp (GPl σ J v) (R v).H H (R v).π (ρ v) (R v).isIrr (hρ v) (hR v)
  choose A hA0 using hA'
  have hA : ∀ v, IsOpFam (R v).π (ρ v) (A v) := hA0
  have hi : ∀ v, IsIsotypic (R v).π (ρ v) := hR
  have hcommπ : ∀ v g, projPl σ J v g = 1 → ∀ y ξ, Commute (π g) (A v y ξ) := fun v g h y ξ =>
    ((hA v).commute (hi v) (C := π g) (fun x => (commute_embPl h x).map π) y ξ).symm
  have hAA : ∀ u v, u ≠ v → ∀ y ξ y' ξ', Commute (A u y ξ) (A v y' ξ') := fun u v huv y ξ y' ξ' =>
    (hA u).commute (hi u) (C := A v y' ξ')
      (fun x => (hcommπ v (embPl σ J u x) (projPl_embPl_ne σ J huv.symm x) y' ξ').symm) y ξ
  obtain ⟨S, w₀, hw₀, hfix₀⟩ := exists_levelOff_fixed (σ := σ) (J := J) hFix L hπ
  have hbad := Filter.eventually_cofinite.1 (eventually_line hAdm hc hJ L)
  set S₁ := S ∪ hbad.toFinset with hS₁
  set s : Finset (Formalism.MainNotions.SchurIrreducible.Pl F) := Finset.univ.image Sum.inl ∪ S₁.image Sum.inr with hs
  have hinl : ∀ w, (Sum.inl w : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s := fun w =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hinr : ∀ v, v ∈ S₁ → (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)
  have hmems : ∀ u ∈ s, ∀ v, u = .inr v → v ∈ S₁ := fun u hu v e => by
    subst e
    rcases Finset.mem_union.1 hu with h | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h
      exact absurd hw (by simp)
    · obtain ⟨v', hv', e⟩ := Finset.mem_image.1 h
      exact Sum.inr_injective e ▸ hv'
  have hoff : levelOff σ J L S₁ ≤ levelOff σ J L S := GlobalTheory.PlaceGen.levelOff_anti σ J L Finset.subset_union_left
  have hKlev : ∀ u, u ∉ s → ∀ k ∈ plK σ J L u, embPl σ J u k ∈ levelOff σ J L S₁ := fun u hu k hk => by
    rcases u with w | v
    · exact absurd (hinl w) hu
    · exact embPl_mem_levelOff (fun h => hu (hinr v h)) hk
  have hgood : ∀ u, ∃ ξ : (R u).H, u ∉ s → ‖ξ‖ = 1 ∧ (∀ k ∈ plK σ J L u, (R u).π k ξ = ξ) ∧
      ∀ h : H, (∀ k ∈ plK σ J L u, ρ u k h = h) → A u ξ ξ h = h := fun u => by
    by_cases hu : u ∈ s
    · exact ⟨0, fun h => absurd hu h⟩
    · rcases u with w | v
      · exact absurd (hinl w) hu
      · have hv : v ∉ hbad.toFinset := fun h => hu (hinr v (Finset.mem_union_right _ h))
        have hl : ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
            (δ : GLoc σ J v →* (X →L[ℂ] X)), IsIrrUnitary δ → ∀ x : X, x ≠ 0 → (∀ k ∈ stabLoc σ J L v, δ k x = x) →
              ∀ y, (∀ k ∈ stabLoc σ J L v, δ k y = y) → ∃ c : ℂ, y = c • x := by
          by_contra hn
          exact hv (hbad.mem_toFinset.2 hn)
        obtain ⟨ξ, h1, h2, h3⟩ := exists_good (hA (.inr v)) (hi (.inr v)) (R (.inr v)).isIrr (hρ (.inr v))
          (plK σ J L (.inr v)) (hl _ _ (R (.inr v)).isIrr) hw₀
          (fun k hk => hfix₀ _ (hoff (hKlev _ hu k hk)))
        exact ⟨ξ, fun _ => ⟨h1, h2, h3⟩⟩
  choose ξg hξg using hgood
  let Inv : H → Prop := fun w => (∀ k ∈ levelOff σ J L S₁, π k w = w) ∧ ∀ u, u ∉ s → A u (ξg u) (ξg u) w = w
  have hproj : ∀ i (ξ : (R i).H), ‖ξ‖ = 1 → A i ξ ξ * A i ξ ξ = A i ξ ξ := fun i ξ h => by
    rw [(hA i).mul (hi i), inner_self_eq_norm_sq_to_K, h]
    simp
  obtain ⟨ξs, w₁, hw₁, hI, hξs⟩ := exists_fixed_of_finset (A := A) hAA
    (fun i w hw => (hA i).exists_ne_zero (hi i) (R i).isIrr (hρ i) hw) hproj Inv s
    (fun i his ξ w hw => ⟨fun k hk => by
        have hc1 := (hcommπ i k (projPl_eq_one_of_mem_levelOff hk (hmems i his)) ξ ξ).eq
        have := DFunLike.congr_fun hc1 w
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hw.1 k hk],
      fun u hu => by
        have hne : u ≠ i := fun e => hu (e ▸ his)
        have := DFunLike.congr_fun (hAA u i hne (ξg u) (ξg u) ξ ξ).eq w
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hw.2 u hu]⟩)
    (w₀ := w₀) ⟨fun k hk => hfix₀ k (hoff hk), fun u hu =>
      (hξg u hu).2.2 w₀ fun k hk => hfix₀ _ (hoff (hKlev u hu k hk))⟩ hw₀
  let ξ : ∀ u, (R u).H := fun u => if u ∈ s then ξs u else ξg u
  have hξ : ∀ u, ‖ξ u‖ = 1 := fun u => by
    by_cases hu : u ∈ s
    · simp only [ξ, if_pos hu]
      exact (hξs u hu).1
    · simp only [ξ, if_neg hu]
      exact (hξg u hu).1
  have hfixall : ∀ u, A u (ξ u) (ξ u) w₁ = w₁ := fun u => by
    by_cases hu : u ∈ s
    · simp only [ξ, if_pos hu]
      exact (hξs u hu).2
    · simp only [ξ, if_neg hu]
      exact hI.2 u hu
  have hn : (‖w₁‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw₁
  set w := (‖w₁‖ : ℂ)⁻¹ • w₁ with hwdef
  have hw1 : ‖w‖ = 1 := by simp [hwdef, norm_smul, hw₁]
  have hlev : ∀ k ∈ levelOff σ J L S₁, π k w = w := fun k hk => by
    rw [hwdef, map_smul, hI.1 k hk]
  let a : ∀ u, (R u).H → (H →L[ℂ] H) := fun u y => A u y (ξ u)
  have hac : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y') := fun i j h y y' => hAA i j h _ _ _ _
  obtain ⟨B, hB⟩ := exists_isRestrTensor (a := a) (ξ := ξ) (w := w) (p := projPl σ J) (e := embPl σ J)
    (δ := fun v => (R v).π) (π := π) hac hπ.irred hξ hw1
    (fun i => by simp only [a, hwdef, map_smul, hfixall i])
    (fun i y y' => by
      simp only [a]
      rw [(hA i).adjoint_eq (hi i) (R i).isIrr (hρ i), (hA i).mul (hi i)])
    (fun i x => projPl_embPl_self σ J i x) (fun i j h x => projPl_embPl_ne σ J h.symm x)
    (fun v g h y => hcommπ v g h y _)
    (fun i x y => (hA i).rep_mul (hi i) x y (ξ i))
    (fun g => by
      obtain ⟨t, ht⟩ := exists_finset_projPl_mem (σ := σ) (J := J) L g
      refine ⟨s ∪ t, fun i hi' => ?_, fun s' hs' k hk1 hk2 => hlev k ?_⟩
      · have h1 : i ∉ s := fun h => hi' (Finset.mem_union_left _ h)
        have h2 : i ∉ t := fun h => hi' (Finset.mem_union_right _ h)
        simp only [ξ, if_neg h1]
        exact (hξg i h1).2.1 _ (ht i h2)
      · refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => hk1 _ (hs' (Finset.mem_union_left _ (hinl w))),
          fun v hv => hk1 _ (hs' (Finset.mem_union_left _ (hinr v hv))), fun v hv => ?_⟩
        by_cases h : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s'
        · have : projPl σ J (.inr v) k = 1 := hk1 _ h
          change projPl σ J (.inr v) k ∈ stabLoc σ J L v
          rw [this]
          exact one_mem _
        · have h3 : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∉ t := fun h' => h (hs' (Finset.mem_union_right _ h'))
          change projPl σ J (.inr v) k ∈ stabLoc σ J L v
          rw [hk2 _ h]
          exact ht _ h3)
  exact ⟨ξ, B, hB⟩

end GlobalTheory.CompanionTheory.RestT

end
