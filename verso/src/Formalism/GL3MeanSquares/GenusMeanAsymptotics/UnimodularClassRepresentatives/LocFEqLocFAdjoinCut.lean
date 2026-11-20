import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinC

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

/- English proof (translation)
Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `LocF.le_locF 𝔭 _ (S.x₀_mem_adjoin T')`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `a ha`.

Take `⟨t, ht, hta⟩` from `(LocF.mem_locF_iff h𝔭 T' a).mp (hT ha)`. Rewrite using `[Submodule.mem_comap, LocF.mem_locF_iff h𝔭]`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_map_of_mem hta)`.
-/
private theorem VecSplit_adjoin_le_locF_of_le_locF (S : VecSplit h h') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    {T T' : Submodule (𝓞 K) V'} (hT : T ≤ locF 𝔭 T') :
    S.adjoin T ≤ locF 𝔭 (S.adjoin T') := by
  refine sup_le ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    exact LocF.le_locF 𝔭 _ (S.x₀_mem_adjoin T')
  · rw [Submodule.map_le_iff_le_comap]
    intro a ha
    obtain ⟨t, ht, hta⟩ := (LocF.mem_locF_iff h𝔭 T' a).mp (hT ha)
    rw [Submodule.mem_comap, LocF.mem_locF_iff h𝔭]
    refine ⟨t, ht, ?_⟩
    rw [← map_smul]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hta)

/- English proof (translation)
Establish `key : ∀ {A B : Submodule (𝓞 K) V'}, locF 𝔭 A = locF 𝔭 B → locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (S.adjoin B)`. Introduce `A B hAB`. Establish `hle` using `VecSplit_adjoin_le_locF_of_le_locF S h𝔭.isPrime ((LocF.le_locF 𝔭 A).trans hAB.le)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_antisymm (key e) (key e.symm)`.
-/
theorem locF_adjoin_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    locF 𝔭 (S.adjoin T) = locF 𝔭 (S.adjoin T') := by
  have key : ∀ {A B : Submodule (𝓞 K) V'}, locF 𝔭 A = locF 𝔭 B →
      locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (S.adjoin B) := by
    intro A B hAB
    have hle := VecSplit_adjoin_le_locF_of_le_locF S h𝔭.isPrime ((LocF.le_locF 𝔭 A).trans hAB.le)
    calc locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (locF 𝔭 (S.adjoin B)) := LocF.locF_mono 𝔭 hle
      _ = locF 𝔭 (S.adjoin B) := LocF.locF_idem 𝔭 _
  exact le_antisymm (key e) (key e.symm)

/- English proof (translation)
Substitute `hm` using the available equality. Rewrite using `[← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭, vd, BallB.discrIdeal_span b hg]`. Simplify using `only [Ideal.span_singleton_le_iff_mem]`.
-/
theorem vd_eq_of_basis (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : finrank K V = m) (b : Basis (Fin m) K V)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = (Matrix.of fun i j => h (b i) (b j)).det) :
    vd h L 𝔭 = sSup {e : ℕ | g₀ ∈ extP K 𝔭 ^ e} := by
  subst hm
  rw [← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭, vd, BallB.discrIdeal_span b hg]
  simp only [Ideal.span_singleton_le_iff_mem]

/- English proof (translation)
Rewrite using `[Fin.range_cons, Submodule.span_insert, VecSplit.adjoin, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem span_range_cons (S : VecSplit h h') {n : ℕ} (x : Fin n → V') :
    Submodule.span (𝓞 K) (Set.range (Fin.cons S.x₀ (fun i => S.ι (x i)) : Fin (n + 1) → V)) =
      S.adjoin (Submodule.span (𝓞 K) (Set.range x)) := by
  rw [Fin.range_cons, Submodule.span_insert, VecSplit.adjoin, Submodule.map_span, ← Set.range_comp]
  rfl

/- English proof (translation)
Establish `hcL : Submodule.IsLattice K (S.cut L)`. Rewrite using `[← S.isLattice_adjoin_iff, S.adjoin_cut h1 hLi hx]`. Conclude with `hL`. Take `⟨b', hb'L, hb'⟩` from `LocalSpans.exists_basis_locF hcL h𝔭`. Establish `hint : ∀ i j, h' (b' i) (b' j) ∈ (1 : Submodule (𝓞 K) K)` using `fun i j => UnimodularLocalization.isIntegralLat_cut S hLi _ (hb'L i) _ (hb'L j)`.

Use `choose H hH using fun i j => Submodule.mem_one.mp (hint i j)`. Establish `hg₀ : algebraMap (𝓞 K) K (Matrix.of H).det = (Matrix.of fun i j => h' (b' i) (b' j)).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[hH]`. Set `c : Fin (finrank K V' + 1) → V` to `Fin.cons S.x₀ (fun i => S.ι (b' i))`. Establish `hli : LinearIndependent K c`. Use `linearIndependent_finCons.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `b'.linearIndependent.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj)`.

Introduce `hmem`. Establish `hle : Submodule.span K (Set.range fun i => S.ι (b' i)) ≤ LinearMap.range S.ι` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b' i, rfl⟩)`. Take `⟨a, ha⟩` from `hle hmem`. Conclude with `S.x₀_not_mem_range a ha`. Establish `hcard : Fintype.card (Fin (finrank K V' + 1)) = finrank K V`.

Rewrite using `[Fintype.card_fin]`. Conclude with `S.finrank_add_one`. Set `bb` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hbb : ⇑bb = c` using `coe_basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hgram : (Matrix.of fun i j => h (bb i) (bb j)).det = (Matrix.of fun i j => h' (b' i) (b' j)).det`.

Rewrite using `[hbb, Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Simplify using `[c, S.orth, h1, Fin.succAbove_zero]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[S.isom]`.

Establish `hspan : locF 𝔭 (Submodule.span (𝓞 K) (Set.range bb)) = locF 𝔭 L`. Rewrite using `[hbb, span_range_cons S b', locF_adjoin_congr hK hF S h𝔭 hb', S.adjoin_cut h1 hLi hx]`. Rewrite using `[vd_eq_of_basis hF h h𝔭 S.finrank_add_one.symm bb hspan (hg₀.trans hgram.symm), vd_eq_of_basis hF h' h𝔭 rfl b' hb' hg₀]`.
-/
theorem vd_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := by
  have hcL : Submodule.IsLattice K (S.cut L) := by
    rw [← S.isLattice_adjoin_iff, S.adjoin_cut h1 hLi hx]
    exact hL
  obtain ⟨b', hb'L, hb'⟩ := LocalSpans.exists_basis_locF hcL h𝔭
  have hint : ∀ i j, h' (b' i) (b' j) ∈ (1 : Submodule (𝓞 K) K) := fun i j =>
    UnimodularLocalization.isIntegralLat_cut S hLi _ (hb'L i) _ (hb'L j)
  choose H hH using fun i j => Submodule.mem_one.mp (hint i j)
  have hg₀ : algebraMap (𝓞 K) K (Matrix.of H).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hH]
  let c : Fin (finrank K V' + 1) → V := Fin.cons S.x₀ (fun i => S.ι (b' i))
  have hli : LinearIndependent K c := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact b'.linearIndependent.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj)
    · intro hmem
      have hle : Submodule.span K (Set.range fun i => S.ι (b' i)) ≤ LinearMap.range S.ι :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b' i, rfl⟩)
      obtain ⟨a, ha⟩ := hle hmem
      exact S.x₀_not_mem_range a ha
  have hcard : Fintype.card (Fin (finrank K V' + 1)) = finrank K V := by
    rw [Fintype.card_fin]
    exact S.finrank_add_one
  let bb := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ⇑bb = c := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hgram : (Matrix.of fun i j => h (bb i) (bb j)).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [hbb, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [c, S.orth, h1, Fin.succAbove_zero]
    congr 1
    ext i j
    simp [S.isom]
  have hspan : locF 𝔭 (Submodule.span (𝓞 K) (Set.range bb)) = locF 𝔭 L := by
    rw [hbb, span_range_cons S b', locF_adjoin_congr hK hF S h𝔭 hb', S.adjoin_cut h1 hLi hx]
  rw [vd_eq_of_basis hF h h𝔭 S.finrank_add_one.symm bb hspan (hg₀.trans hgram.symm),
    vd_eq_of_basis hF h' h𝔭 rfl b' hb' hg₀]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `LocalizedFibreSets.exists_max_over (K := K) h𝔭`. Simplify using `only [locF_eq_loc hK hF hP] at hx ⊢`. Use `UnimodularLocalization.loc_eq_loc_adjoin_cut S hP.isPrime hBi hx ?_` and prove the remaining obligations. Rewrite using `[h1, inv_one]`. Conclude with `⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩`.
-/
theorem locF_eq_locF_adjoin_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    locF 𝔭 B = locF 𝔭 (S.adjoin (S.cut B)) := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  simp only [locF_eq_loc hK hF hP] at hx ⊢
  refine UnimodularLocalization.loc_eq_loc_adjoin_cut S hP.isPrime hBi hx ?_
  rw [h1, inv_one]
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

/- English proof (translation)
Establish `e5` using `locF_eq_locF_adjoin_cut hK hF S h1 hBi h𝔭 hx`. Establish `hcB : Submodule.IsLattice K (S.cut B)` using `StabilizerLattices.isLattice_cut S hB`. Establish `hcBi` using `UnimodularLocalization.isIntegralLat_cut S hBi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← vd_cut hK hF hs hd S h1 ((S.isLattice_adjoin_iff _).mpr hcB) ((S.isIntegralLat_adjoin_iff hs h1 _).mpr hcBi) (S.x₀_mem_adjoin _) h𝔭, S.cut_adjoin]`.

Use `_ = vd h B 𝔭 := by rw [← localizedQuotients.vd_locF hF h _ h𝔭, ← e5, localizedQuotients.vd_locF hF h _ h𝔭]`.
-/
theorem vd_cut_of_mem_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = vd h B 𝔭 := by
  have e5 := locF_eq_locF_adjoin_cut hK hF S h1 hBi h𝔭 hx
  have hcB : Submodule.IsLattice K (S.cut B) := StabilizerLattices.isLattice_cut S hB
  have hcBi := UnimodularLocalization.isIntegralLat_cut S hBi
  calc vd h' (S.cut B) 𝔭 = vd h (S.adjoin (S.cut B)) 𝔭 := by
        rw [← vd_cut hK hF hs hd S h1 ((S.isLattice_adjoin_iff _).mpr hcB)
          ((S.isIntegralLat_adjoin_iff hs h1 _).mpr hcBi) (S.x₀_mem_adjoin _) h𝔭, S.cut_adjoin]
    _ = vd h B 𝔭 := by rw [← localizedQuotients.vd_locF hF h _ h𝔭, ← e5, localizedQuotients.vd_locF hF h _ h𝔭]

/- English proof (translation)
Establish `hML : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L)` using `LocalizedFibreSets.isLattice_gmap g hL`. Establish `hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L)` using `UnimodularLocalization.isIntegralLat_gmap hg hLi`. Establish `hxM : S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L)` using `by rwa [← LocalizedFibreSets.gmap_locF]`. Establish `hxL : S.x₀ ∈ locF 𝔭 L` using `LocF.le_locF 𝔭 L hx`. Establish `hvA : vd h' (S.cut L) 𝔭 = vd h L 𝔭` using `vd_cut hK hF hs hd S h1 hL hLi hx h𝔭`.

Establish `hvB : vd h' (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) 𝔭 = vd h L 𝔭`. Rewrite using `[vd_cut_of_mem_locF hK hF hs hd S h1 hML hMi h𝔭 hxM, UnimodularLocalization.vd_gmap hg]`. Establish `hA` using `StabilizerLattices.isLattice_cut S hL`. Establish `hB` using `StabilizerLattices.isLattice_cut S hML`. Establish `hAi` using `UnimodularLocalization.isIntegralLat_cut S hLi`.

Establish `hBi` using `UnimodularLocalization.isIntegralLat_cut S hMi`. Establish `hs' : h'.IsSymm` using `S.isSymm hs`. Establish `hd' : IsTotPosDef h'` using `S.isTotPosDef hd`. Choose the witnesses or unpack the hypotheses as in `⟨g', hg', hg'e⟩ : ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) := by`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h0` into its components or cases.

Conclude with `exists_isom_locF_of_vd_zero hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0) (hvB.trans h0)`. Conclude with `exists_isom_locF_of_vd_one hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0) (hvB.trans h0)`. Use `⟨g', hg', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg'e, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]`. Rewrite using `[LocalizedFibreSets.gmap_locF g 𝔭 L, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL, LocalizedFibreSets.gmap_locF, SplitBAux.gmap_extOf S g' rfl, locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hxM]`.

Conclude with `locF_adjoin_congr hK hF S h𝔭 (by rw [← LocalizedFibreSets.gmap_locF]; exact hg'e)`.
-/
theorem exists_isom_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) := by
  have hML : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := LocalizedFibreSets.isLattice_gmap g hL
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) := UnimodularLocalization.isIntegralLat_gmap hg hLi
  have hxM : S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) := by rwa [← LocalizedFibreSets.gmap_locF]
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  have hvA : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := vd_cut hK hF hs hd S h1 hL hLi hx h𝔭
  have hvB : vd h' (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) 𝔭 = vd h L 𝔭 := by
    rw [vd_cut_of_mem_locF hK hF hs hd S h1 hML hMi h𝔭 hxM, UnimodularLocalization.vd_gmap hg]
  have hA := StabilizerLattices.isLattice_cut S hL
  have hB := StabilizerLattices.isLattice_cut S hML
  have hAi := UnimodularLocalization.isIntegralLat_cut S hLi
  have hBi := UnimodularLocalization.isIntegralLat_cut S hMi
  have hs' : h'.IsSymm := S.isSymm hs
  have hd' : IsTotPosDef h' := S.isTotPosDef hd
  obtain ⟨g', hg', hg'e⟩ : ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h',
      Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h0
    · exact exists_isom_locF_of_vd_zero hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
    · exact exists_isom_locF_of_vd_one hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
  refine ⟨g', hg', ?_, ?_⟩
  · rw [hg'e, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
  · rw [LocalizedFibreSets.gmap_locF g 𝔭 L, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL, LocalizedFibreSets.gmap_locF,
      SplitBAux.gmap_extOf S g' rfl, locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hxM]
    exact locF_adjoin_congr hK hF S h𝔭 (by rw [← LocalizedFibreSets.gmap_locF]; exact hg'e)

/- English proof (translation)
Establish `hxL : S.x₀ ∈ locF 𝔭 L` using `LocF.le_locF 𝔭 L hx`. Rewrite using `[fibLoc, Nat.card_eq_one_iff_exists]`. Use `⟨⟨locF 𝔭 L, LocF.locF_idem 𝔭 L, ⟨1, one_mem _, autSub_gmap_one _⟩, hxL, by rw [LocalizedFibreSets.cut_locF, LocF.locF_idem]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨Λ, -, ⟨g, hg, rfl⟩, hΛx, hΛc⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L`. Establish `hMi` using `UnimodularLocalization.isIntegralLat_gmap hg hLi`. Rewrite `hΛx`, `hΛc`, the goal using `[LocalizedFibreSets.gmap_locF]`. Rewrite using `[locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hΛx, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL]`. Apply `locF_adjoin_congr hK hF S h𝔭` to reduce the goal to its premises.

Rewrite using `[← LocalizedFibreSets.cut_locF, hΛc, LocF.locF_idem]`.
-/
theorem fibLoc_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : fibLoc S L 𝔭 (locF 𝔭 (S.cut L)) = 1 := by
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  rw [fibLoc, Nat.card_eq_one_iff_exists]
  refine ⟨⟨locF 𝔭 L, LocF.locF_idem 𝔭 L, ⟨1, one_mem _, autSub_gmap_one _⟩, hxL,
    by rw [LocalizedFibreSets.cut_locF, LocF.locF_idem]⟩, ?_⟩
  rintro ⟨Λ, -, ⟨g, hg, rfl⟩, hΛx, hΛc⟩
  apply Subtype.ext
  show Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L
  have hMi := UnimodularLocalization.isIntegralLat_gmap hg hLi
  rw [LocalizedFibreSets.gmap_locF] at hΛx hΛc ⊢
  rw [locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hΛx,
    locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL]
  apply locF_adjoin_congr hK hF S h𝔭
  rw [← LocalizedFibreSets.cut_locF, hΛc, LocF.locF_idem]

/- English proof (translation)
Establish `hcLi` using `UnimodularLocalization.isIntegralLat_cut S hLi`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `T hT`. Rewrite `hT` using `[Finset.mem_singleton]`. Substitute `hT` using the available equality.

Use `⟨LocF.locF_idem 𝔭 _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hcLi, ?_⟩` and prove the remaining obligations. Rewrite using `[fibLoc_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv]`. Conclude with `one_ne_zero`. Introduce `T hT _ hf`. Use `⟨locF 𝔭 (S.cut L), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩` and prove the remaining obligations.

Take `⟨g, hg, hgx, hgT⟩` from `UnimodularLocalization.exists_of_fibLoc_ne_zero S hf`. Rewrite `hgx` using `[← LocalizedFibreSets.gmap_locF]`. Take `⟨g', hg', he, -⟩` from `exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg hgx`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Rewrite using `[he, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF, hgT, hT]`.

Introduce and unpack `T₀ ⟨hT₀, -⟩`. Conclude with `Finset.mem_singleton.mp hT₀`.
-/
theorem isLocReps_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : IsLocReps S L 𝔭 {locF 𝔭 (S.cut L)} := by
  have hcLi := UnimodularLocalization.isIntegralLat_cut S hLi
  refine ⟨?_, ?_⟩
  · intro T hT
    rw [Finset.mem_singleton] at hT
    subst hT
    refine ⟨LocF.locF_idem 𝔭 _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hcLi, ?_⟩
    rw [fibLoc_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv]
    exact one_ne_zero
  · intro T hT _ hf
    refine ⟨locF 𝔭 (S.cut L), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · obtain ⟨g, hg, hgx, hgT⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hf
      rw [← LocalizedFibreSets.gmap_locF] at hgx
      obtain ⟨g', hg', he, -⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg hgx
      refine ⟨g', hg', ?_⟩
      rw [he, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF, hgT, hT]
    · rintro T₀ ⟨hT₀, -⟩
      exact Finset.mem_singleton.mp hT₀

/- English proof (translation)
Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hyy`. Take `⟨g₁, hg₁, hg₁y⟩` from `exists_isom_map_of_eq hK hs hd hy0 (hyy.trans h1.symm)`. Establish `hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)`.

Rewrite using `[← hg₁y]`. Conclude with `Submodule.mem_map_of_mem hy`. Take `⟨g', hg', -, he⟩` from `exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg₁ hxg`. Use `⟨g₁⁻¹ * SplitBAux.extOf S g', ⟨mul_mem (inv_mem hg₁) (SplitBAux.extOf_mem_isom hs S hg'), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[autSub_gmap_mul, he, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]`.

Use `show g₁⁻¹ (SplitBAux.extOf S g' S.x₀) = y`. Rewrite using `[SplitBAux.extOf_x₀, ← hg₁y]`. Conclude with `g₁.symm_apply_apply y`.
-/
theorem exists_aut_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {y : V} (hy : y ∈ locF 𝔭 L) (hyy : h y y = 1) :
    ∃ g ∈ autSub h (locF 𝔭 L), g S.x₀ = y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyy
  obtain ⟨g₁, hg₁, hg₁y⟩ := exists_isom_map_of_eq hK hs hd hy0 (hyy.trans h1.symm)
  have hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L) := by
    rw [← hg₁y]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨g', hg', -, he⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg₁ hxg
  refine ⟨g₁⁻¹ * SplitBAux.extOf S g', ⟨mul_mem (inv_mem hg₁) (SplitBAux.extOf_mem_isom hs S hg'), ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, he, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · show g₁⁻¹ (SplitBAux.extOf S g' S.x₀) = y
    rw [SplitBAux.extOf_x₀, ← hg₁y]
    exact g₁.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.PinC
