import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

/- English proof (translation)
Establish `hc : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f`. Apply `Subgroup.topologicalClosure_minimal` to reduce the goal to its premises. Rewrite using `[commutator_def, Subgroup.commutator_le]`. Introduce `a _ b _`. Rewrite using `[Subgroup.mem_comap, map_commutatorElement]`.

Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`. Conclude with `(Subgroup.isClosed_topologicalClosure _).preimage hf`. Conclude with `⟨QuotientGroup.map _ _ f hc, fun g => rfl⟩`.
-/
private theorem ab_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G',
      ∀ g : G, F (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (f g) := by
  have hc : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.le_topologicalClosure _
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  exact ⟨QuotientGroup.map _ _ f hc, fun g => rfl⟩

/- English proof (translation)
Take `⟨k, hk⟩` from `(Iff.rfl : x ∈ CommGroup.primaryComponent A l ↔ ∃ k : ℕ, x ^ l ^ k = 1).mp hx`. Conclude with `(Iff.rfl : F x ∈ CommGroup.primaryComponent B l ↔ ∃ k : ℕ, F x ^ l ^ k = 1).mpr ⟨k, by rw [← map_pow, hk, map_one]⟩`.
-/
private theorem map_prim {A B : Type} [CommGroup A] [CommGroup B] (l : ℕ) [Fact l.Prime] (F : A →* B) {x : A}
    (hx : x ∈ CommGroup.primaryComponent A l) : F x ∈ CommGroup.primaryComponent B l := by
  obtain ⟨k, hk⟩ := (Iff.rfl : x ∈ CommGroup.primaryComponent A l ↔ ∃ k : ℕ, x ^ l ^ k = 1).mp hx
  exact (Iff.rfl : F x ∈ CommGroup.primaryComponent B l ↔ ∃ k : ℕ, F x ^ l ^ k = 1).mpr
    ⟨k, by rw [← map_pow, hk, map_one]⟩

open UpperTheory.V.W in
/- English proof (translation)
Take `⟨Fe, hFe⟩` from `ab_map e.toMonoidHom he`. Take `⟨Fs, hFs⟩` from `ab_map e.symm.toMonoidHom he'`. Establish `mu1 : ∀ g, g ∈ muG l G → e g ∈ muG l G'`. Introduce `g hg`. Establish `h1` using `map_prim l Fe (x := QuotientGroup.mk' (commutator G).topologicalClosure g) hg`.

Establish `h2` using `hFe g`. Simplify using `only [MulEquiv.coe_toMonoidHom] at h2`. Rewrite `h1` using `[h2]`. Conclude with `h1`. Establish `mu2 : ∀ g', g' ∈ muG l G' → e.symm g' ∈ muG l G`.

Introduce `g hg`. Establish `h1` using `map_prim l Fs (x := QuotientGroup.mk' (commutator G').topologicalClosure g) hg`. Establish `h2` using `hFs g`. Simplify using `only [MulEquiv.coe_toMonoidHom] at h2`. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Set `bm : CommGroup.primaryComponent (TopologicalAbelianization G') l →* CommGroup.primaryComponent (TopologicalAbelianization G) l` to `MonoidHom.codRestrict (Fs.comp (CommGroup.primaryComponent _ l).subtype) _ (fun x => map_prim l Fs x.2)`. Use `⟨LocAb.mk (A.a.comp e.toMonoidHom) (A.cont.comp he) (A.surj.comp e.surjective) ?_ ?_ ((bm.comp A.b).comp e.toMonoidHom) ?_ ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[← A.inertia x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, h⟩`. Conclude with `⟨e g, (hI g).2 hg, h⟩`. Introduce and unpack `⟨g', hg', h⟩`. Conclude with `⟨e.symm g', (hI _).1 (by simpa using hg'), by simpa using h⟩`.

Introduce `C _ _ hC χ hχo hmu`. Establish `key` using `A.univ C hC (χ.comp e.symm.toMonoidHom) (hχo.preimage he') (by`. Introduce `g' hg'`. Conclude with `(MonoidHom.mem_ker).1 (hmu (mu2 g' hg')))`. Introduce `g hg`.

Establish `h3 : e g ∈ (χ.comp e.symm.toMonoidHom).ker` using `key (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg))`. Establish `h5` using `MonoidHom.mem_ker.1 h3`. Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h5`. Conclude with `MonoidHom.mem_ker.2 h5`. Use `Subgroup.isOpen_mono (H₁ := A.b.ker.comap e.toMonoidHom) ?_ (A.b_open.preimage he)` and prove the remaining obligations.

Introduce `g hg`. Rewrite `hg` using `[Subgroup.mem_comap, MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one]`. Introduce `g hg show Fs ((A.b (e g)) : TopologicalAbelianization G') = _`. Rewrite using `[A.b_mu _ (mu1 g hg)]`.

Establish `h4` using `hFs (e g)`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4`. Conclude with `h4`.
-/
private theorem locAb_transport (l : ℕ) [Fact l.Prime] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃* G') (he : Continuous e) (he' : Continuous e.symm)
    (I : Subgroup G) (I' : Subgroup G') (hI : ∀ g, e g ∈ I' ↔ g ∈ I) (d : ℕ) (A : LocAb l G' I' d) :
    Nonempty (LocAb l G I d) := by
  obtain ⟨Fe, hFe⟩ := ab_map e.toMonoidHom he
  obtain ⟨Fs, hFs⟩ := ab_map e.symm.toMonoidHom he'
  have mu1 : ∀ g, g ∈ muG l G → e g ∈ muG l G' := by
    intro g hg
    have h1 := map_prim l Fe (x := QuotientGroup.mk' (commutator G).topologicalClosure g) hg
    have h2 := hFe g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  have mu2 : ∀ g', g' ∈ muG l G' → e.symm g' ∈ muG l G := by
    intro g hg
    have h1 := map_prim l Fs (x := QuotientGroup.mk' (commutator G').topologicalClosure g) hg
    have h2 := hFs g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  let bm : CommGroup.primaryComponent (TopologicalAbelianization G') l →*
      CommGroup.primaryComponent (TopologicalAbelianization G) l :=
    MonoidHom.codRestrict (Fs.comp (CommGroup.primaryComponent _ l).subtype) _
      (fun x => map_prim l Fs x.2)
  refine ⟨LocAb.mk (A.a.comp e.toMonoidHom) (A.cont.comp he) (A.surj.comp e.surjective) ?_ ?_
    ((bm.comp A.b).comp e.toMonoidHom) ?_ ?_⟩
  · intro x
    rw [← A.inertia x]
    constructor
    · rintro ⟨g, hg, h⟩
      exact ⟨e g, (hI g).2 hg, h⟩
    · rintro ⟨g', hg', h⟩
      exact ⟨e.symm g', (hI _).1 (by simpa using hg'), by simpa using h⟩
  · intro C _ _ hC χ hχo hmu
    have key := A.univ C hC (χ.comp e.symm.toMonoidHom) (hχo.preimage he') (by
      intro g' hg'
      exact (MonoidHom.mem_ker).1 (hmu (mu2 g' hg')))
    intro g hg
    have h3 : e g ∈ (χ.comp e.symm.toMonoidHom).ker :=
      key (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg))
    have h5 := MonoidHom.mem_ker.1 h3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h5
    exact MonoidHom.mem_ker.2 h5
  · refine Subgroup.isOpen_mono (H₁ := A.b.ker.comap e.toMonoidHom) ?_ (A.b_open.preimage he)
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one]
  · intro g hg
    show Fs ((A.b (e g)) : TopologicalAbelianization G') = _
    rw [A.b_mu _ (mu1 g hg)]
    have h4 := hFs (e g)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4
    exact h4

open Formalism.BasicNotions.Loc in
/- English proof (translation)
Introduce `l _ F Ω _ _ _ _ _ _ A w hA hl`. Take `⟨j, hj⟩` from `(UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hA hl`. Substitute `hj` using the available equality. Take `⟨-, φ, hφ, -, hran, hin, -, hidx⟩` from `(UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j`. Set `K : FinExt l` to `⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩`.

Establish `hK : ∀ τ, τ ∈ GK K ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x)` using `GlobalTheory.PlaceBridge.mem_GK_iff (E := F) (Ω := Ω) K rfl`. Establish `hR : φ.range = GK K`. Use extensionality with `τ`. Rewrite using `[hran τ, hK τ]`. Establish `hd : Module.finrank ℚ_[l] K.1 = locDeg w`.

Rewrite using `[IntermediateField.finrank_eq_fixingSubgroup_index, ← hidx w hA, hR]`. Both sides reduce to the same expression. Take `⟨B⟩` from `UpperTheory.V.W.lam_local l K`. Rewrite `B` using `[hd]`. Set `e` to `(MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hR)`.

Use `locAb_transport l e ?_ ?_ _ _ ?_ _ B` and prove the remaining obligations. Conclude with `continuous_induced_rng.2 hφ.continuous`. Use `hφ.toIsEmbedding.continuous_iff.2 ?_` and prove the remaining obligations. Establish `h : (⇑φ ∘ ⇑e.symm) = Subtype.val` using `funext fun τ => congrArg Subtype.val (e.apply_symm_apply τ)`. Rewrite using `[h]`.

Conclude with `continuous_subtype_val`. Introduce `g`. Rewrite using `[Subgroup.mem_comap, Subgroup.mem_subgroupOf]`. Conclude with `hin g`.
-/
theorem UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place :
    ∀ (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Nonempty (UpperTheory.V.W.LocAb l (Dec (F := F) A) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) (locDeg w)) := by
  intro l _ F Ω _ _ _ _ _ _ A w hA hl
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hA hl
  subst hj
  obtain ⟨-, φ, hφ, -, hran, hin, -, hidx⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK : ∀ τ, τ ∈ GK K ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x) :=
    GlobalTheory.PlaceBridge.mem_GK_iff (E := F) (Ω := Ω) K rfl
  have hR : φ.range = GK K := by
    ext τ
    rw [hran τ, hK τ]
  have hd : Module.finrank ℚ_[l] K.1 = locDeg w := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← hidx w hA, hR]
    rfl
  obtain ⟨B⟩ := UpperTheory.V.W.lam_local l K
  rw [hd] at B
  let e := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hR)
  refine locAb_transport l e ?_ ?_ _ _ ?_ _ B
  · exact continuous_induced_rng.2 hφ.continuous
  · refine hφ.toIsEmbedding.continuous_iff.2 ?_
    have h : (⇑φ ∘ ⇑e.symm) = Subtype.val := funext fun τ => congrArg Subtype.val (e.apply_symm_apply τ)
    rw [h]
    exact continuous_subtype_val
  · intro g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hin g
