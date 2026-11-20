import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

namespace GlobalTheory.LevelActAnyField

section Moduli

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelActionLaws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H}

/- English proof (translation)
Take `⟨g, h1, h2, h3⟩` from `hs`. Take `⟨ρ, hs, ν, hM, hAA⟩` from `exists_levAut hpq Xo g h3`. Use `⟨ρ.hom, ν, inferInstance, hs, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← eta_congr Xo (h1 a)]`. Conclude with `hM a`.

Establish `e` using `hAA a`. Rewrite `e` using `[etaA_congr Xo (h2 a)]`. Conclude with `e`.
-/
theorem exists_move_of_sim (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (f : D.La →ₗ[𝓞 E] D.La)
    (hs : ∃ g : Sim D, (∀ a, g.f l.M a - f a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (g.f l.A a - a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) :
    ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧ IsLevMove ρ ν f LinearMap.id := by
  obtain ⟨g, h1, h2, h3⟩ := hs
  obtain ⟨ρ, hs, ν, hM, hAA⟩ := exists_levAut hpq Xo g h3
  refine ⟨ρ.hom, ν, inferInstance, hs, fun a => ?_, fun a => ?_⟩
  · rw [← eta_congr Xo (h1 a)]; exact hM a
  · have e := hAA a
    rw [etaA_congr Xo (h2 a)] at e
    exact e

/- English proof (translation)
Take `⟨ρ', ν', i', h', hm⟩` from `hy`. Take `⟨rfl, e⟩` from `GlobalTheory.levMove_unique E H D l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h h' hs`. Take `⟨⟨w, hw⟩, hu⟩` from `GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y`. Rewrite using `[← hu w y' ν' e.symm hw hm]` and apply the resulting hypothesis.
-/
theorem frMove_transfer' (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (c : Coeff l) (f : D.La →ₗ[𝓞 E] D.La)
    (hs : ∃ g : Sim D, (∀ a, g.f l.M a - f a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (g.f l.A a - a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} (i : IsIso ρ)
    (h : IsLevMove ρ ν f LinearMap.id) {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S}
    (hy : levR (f, LinearMap.id) y y') : FrMove ρ ν y y' := by
  obtain ⟨ρ', ν', i', h', hm⟩ := hy
  obtain ⟨rfl, e⟩ := GlobalTheory.levMove_unique E H D l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp)
    (fun a => ⟨0, by simp⟩) i i' h h' hs
  obtain ⟨⟨w, hw⟩, hu⟩ := GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y
  rwa [← hu w y' ν' e.symm hw hm]

/- English proof (translation)
Establish `hs : ∀ g : G, ∃ s : Sim D, (∀ a, s.f l.M a - lev g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ (∀ a, D.ModN l.A (s.f l.A a - a)) ∧ (l.A : ℤ) ∣ s.ν l.A - 1` using `fun g => by`. Use `GlobalTheory.exists_sim_of_aut_mod E H D l l.A (lev g) hpq l.A_pos hA fun x hx => ?_` and prove the remaining obligations. Establish `a1 : lev g⁻¹ (lev g x) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)`. Use `Submodule.mem_map_of_mem (f := lev g⁻¹) hx` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top this`. Establish `a2` using `hm g⁻¹ g x`. Rewrite `a2` using `[inv_mul_cancel]`. Establish `e : x = (lev 1 x - lev g⁻¹ (lev g x)) + lev g⁻¹ (lev g x) - (lev 1 x - x)` using `by abel`. Rewrite using `[e]`.

Conclude with `sub_mem (add_mem a2 a1) (h1 x)`. Take `⟨⟨ι, hι, hone⟩, hmul, hnb⟩` from `GlobalTheory.MoveCalc.frMove_calculus E H D l Xo c`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g S _ _ y`. Take `⟨ρ, ν, i, h⟩` from `exists_move_of_sim hpq Xo _ (hs g)`.

Take `⟨y', hy'⟩` from `(GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y).1`. Conclude with `⟨y', ρ, ν, i, h, hy'⟩`. Introduce `g S _ _ y y' y'' h' h''`. Take `⟨ρ, ν, i, h, hm⟩` from `h'`. Establish `hm'` using `frMove_transfer' hpq Xo c _ (hs g) i h h''`.

Take `rfl` from `(GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'`. Conclude with `(GlobalTheory.Frames.frMap_unique_refl_iff E H D l Xo c S S (AlgHom.id c.F S) y').2.1`. Introduce `S _ _ y`. Use `⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩` and prove the remaining obligations. Rewrite using `[hι, Category.comp_id, Category.id_comp]`.

Conclude with `congrArg _ (eta_congr Xo (h1 a))`. Rewrite using `[hι, Category.comp_id, Category.id_comp]`. Both sides reduce to the same expression. Introduce `g g' S _ _ y y' y'' h h'`. Take `⟨ρ, ν, i, h, hv⟩` from `h`.

Take `⟨ρ', ν', i', h', hv'⟩` from `h'`. Take `⟨μ, hμ, hc⟩` from `hmul ρ ρ' ν ν'`. Use `⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hv hv'⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h'.1, h.1]`. Establish `e : Xo.univ.eta (lev (g * g') a) = Xo.univ.eta (lev g (lev g' a))` using `eta_congr Xo (hm g g' a)`.

Establish `b1 : (Xo.univ.eta (lev g (lev g' a))).left ≫ ν.φ = ρ ≫ (Xo.univ.eta (lev g' a)).left` using `h.2.1 _`. Establish `b2 : (Xo.univ.eta (lev g' a)).left ≫ ν'.φ = ρ' ≫ (Xo.univ.eta a).left` using `h'.2.1 _`. Use `show (Xo.univ.eta (lev (g * g') a)).left ≫ μ.φ = _`. Rewrite using `[e, hμ, ← Category.assoc, b1, Category.assoc, b2, Category.assoc]`. Establish `b1 : (Xo.univ.etaA a).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left` using `h.2.2 _`.

Establish `b2 : (Xo.univ.etaA a).left ≫ ν'.φ = ρ' ≫ (Xo.univ.etaA a).left` using `h'.2.2 _`. Use `show (Xo.univ.etaA a).left ≫ μ.φ = _`. Rewrite using `[hμ, ← Category.assoc, b1, Category.assoc, b2, Category.assoc]`. Introduce `g S T _ _ _ _ φ y y' z z' hyz hy hz`. Take `⟨ρ, ν, i, h, hm⟩` from `hy`.

Conclude with `(hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer' hpq Xo c _ (hs g) i h hz)`. Introduce `g S _ _ t y y' z z' hyz hy hz`. Take `⟨ρ, ν, i, h, hm⟩` from `hy`. Conclude with `(hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer' hpq Xo c _ (hs g) i h hz)`.
-/
theorem actLaws_of_action_mod (hpq : 1 ≤ D.p + D.q) (hA : l.A.Coprime l.M) (Xo : Moduli D l) (c : Coeff l)
    {G : Type} [Group G] (lev : G → D.La →ₗ[𝓞 E] D.La)
    (h1 : ∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (hm : ∀ g g' a, lev (g * g') a - lev g (lev g' a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
        levActR (Xo := Xo) (c := c) (fun g => (lev g, LinearMap.id)) g' y y') := by
  have hs : ∀ g : G, ∃ s : Sim D, (∀ a, s.f l.M a - lev g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      (∀ a, D.ModN l.A (s.f l.A a - a)) ∧ (l.A : ℤ) ∣ s.ν l.A - 1 := fun g => by
    refine GlobalTheory.exists_sim_of_aut_mod E H D l l.A (lev g) hpq l.A_pos hA fun x hx => ?_
    have a1 : lev g⁻¹ (lev g x) ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.mem_map_of_mem (f := lev g⁻¹) hx
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have a2 := hm g⁻¹ g x
    rw [inv_mul_cancel] at a2
    have e : x = (lev 1 x - lev g⁻¹ (lev g x)) + lev g⁻¹ (lev g x) - (lev 1 x - x) := by abel
    rw [e]
    exact sub_mem (add_mem a2 a1) (h1 x)
  obtain ⟨⟨ι, hι, hone⟩, hmul, hnb⟩ := GlobalTheory.MoveCalc.frMove_calculus E H D l Xo c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨ρ, ν, i, h⟩ := exists_move_of_sim hpq Xo _ (hs g)
    obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y).1
    exact ⟨y', ρ, ν, i, h, hy'⟩
  · intro g S _ _ y y' y'' h' h''
    obtain ⟨ρ, ν, i, h, hm⟩ := h'
    have hm' := frMove_transfer' hpq Xo c _ (hs g) i h h''
    obtain rfl := (GlobalTheory.exists_unique_frMove E H D l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H D l Xo c S S (AlgHom.id c.F S) y').2.1
  · intro S _ _ y
    refine ⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (eta_congr Xo (h1 a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  · intro g g' S _ _ y y' y'' h h'
    obtain ⟨ρ, ν, i, h, hv⟩ := h
    obtain ⟨ρ', ν', i', h', hv'⟩ := h'
    obtain ⟨μ, hμ, hc⟩ := hmul ρ ρ' ν ν'
    refine ⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hv hv'⟩
    · rw [Category.assoc, h'.1, h.1]
    · have e : Xo.univ.eta (lev (g * g') a) = Xo.univ.eta (lev g (lev g' a)) := eta_congr Xo (hm g g' a)
      have b1 : (Xo.univ.eta (lev g (lev g' a))).left ≫ ν.φ = ρ ≫ (Xo.univ.eta (lev g' a)).left := h.2.1 _
      have b2 : (Xo.univ.eta (lev g' a)).left ≫ ν'.φ = ρ' ≫ (Xo.univ.eta a).left := h'.2.1 _
      show (Xo.univ.eta (lev (g * g') a)).left ≫ μ.φ = _
      rw [e, hμ, ← Category.assoc, b1, Category.assoc, b2, Category.assoc]
    · have b1 : (Xo.univ.etaA a).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left := h.2.2 _
      have b2 : (Xo.univ.etaA a).left ≫ ν'.φ = ρ' ≫ (Xo.univ.etaA a).left := h'.2.2 _
      show (Xo.univ.etaA a).left ≫ μ.φ = _
      rw [hμ, ← Category.assoc, b1, Category.assoc, b2, Category.assoc]
  · intro g S T _ _ _ _ φ y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer' hpq Xo c _ (hs g) i h hz)
  · intro g S _ _ t y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer' hpq Xo c _ (hs g) i h hz)

/- English proof (translation)
Establish `h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l` using `by rw [Mfr, l.coprime]; trivial`. Take `⟨e, he, e', he', hs⟩` from `Submodule.mem_sup.1 h1`. Take `⟨b, hb⟩` from `h (e' • a) (Submodule.smul_mem_smul he' trivial)`. Establish `hM : (l.M : 𝓞 E) ∈ l.Mb`. Rewrite using `[← Ideal.span_singleton_le_iff_mem, ← l.prod]`.

Conclude with `Ideal.mul_le_left`. Establish `: f a = e • f a + (l.M : 𝓞 E) • b`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← hb, map_smul, ← add_smul, hs, one_smul]`. Rewrite using `[this]`. Conclude with `add_mem (Submodule.smul_mem_smul he trivial) (Submodule.smul_mem_smul hM trivial)`.
-/
theorem mem_of_half (f : D.La →ₗ[𝓞 E] D.La)
    (h : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) D.La), ∃ b, f a = l.M • b) (a : D.La) :
    f a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; trivial
  obtain ⟨e, he, e', he', hs⟩ := Submodule.mem_sup.1 h1
  obtain ⟨b, hb⟩ := h (e' • a) (Submodule.smul_mem_smul he' trivial)
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    rw [← Ideal.span_singleton_le_iff_mem, ← l.prod]
    exact Ideal.mul_le_left
  have : f a = e • f a + (l.M : 𝓞 E) • b := by
    rw [Nat.cast_smul_eq_nsmul, ← hb, map_smul, ← add_smul, hs, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem_smul he trivial) (Submodule.smul_mem_smul hM trivial)

end Moduli

section Frames

open NumberField IsDedekindDomain Formalism.L2.DIV Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Unfold `resS at h`. Rewrite `h` using `[RingHom.comp_apply]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h)`.
-/
theorem mem_idS_of_resS (PP : Pl E) (s : Formalism.L2.Herm.intAf F E) (h : resS F PP s = 0) : s ∈ idS F PP.asIdeal := by
  unfold resS at h
  rw [RingHom.comp_apply] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h)

/- English proof (translation)
Establish `e : idS F (∏ PP ∈ Pg, PP.asIdeal) = ∏ PP ∈ Pg, idS F PP.asIdeal` using `map_prod (Ideal.mapHom (oToS F E)) _ _`. Rewrite using `[e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun PP : Pl E => idS F PP.asIdeal) (fun a _ b _ hab => (HeightOneSpectrum.isCoprime_of_ne a b hab).map (Ideal.mapHom (oToS F E)))]`. Simplify using `only [Submodule.mem_iInf]`. Conclude with `fun PP hP => mem_idS_of_resS PP s (h PP hP)`.
-/
theorem mem_idS_prod (Pg : Finset (Pl E)) (s : Formalism.L2.Herm.intAf F E) (h : ∀ PP ∈ Pg, resS F PP s = 0) :
    s ∈ idS F (∏ PP ∈ Pg, PP.asIdeal) := by
  have e : idS F (∏ PP ∈ Pg, PP.asIdeal) = ∏ PP ∈ Pg, idS F PP.asIdeal :=
    map_prod (Ideal.mapHom (oToS F E)) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun PP : Pl E => idS F PP.asIdeal)
    (fun a _ b _ hab => (HeightOneSpectrum.isCoprime_of_ne a b hab).map (Ideal.mapHom (oToS F E)))]
  simp only [Submodule.mem_iInf]
  exact fun PP hP => mem_idS_of_resS PP s (h PP hP)

/- English proof (translation)
Establish `h1 : s * oToS F E b ∈ idS F (I * J)`. Unfold `idS`. Rewrite using `[Ideal.map_mul]`. Conclude with `Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem _ hb)`. Rewrite `h1` using `[hIJ, idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton]`.

Take `⟨t, ht⟩` from `h1`. Conclude with `⟨t, by rw [mul_comm, ht]⟩`.
-/
theorem exists_div {I J : Ideal (𝓞 E)} {M : ℕ} (hIJ : I * J = Ideal.span {(M : 𝓞 E)}) {b : 𝓞 E} (hb : b ∈ J)
    {s : Formalism.L2.Herm.intAf F E} (hs : s ∈ idS F I) : ∃ t, oToS F E b * s = (M : Formalism.L2.Herm.intAf F E) * t := by
  have h1 : s * oToS F E b ∈ idS F (I * J) := by
    unfold idS
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem _ hb)
  rw [hIJ, idS, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at h1
  obtain ⟨t, ht⟩ := h1
  exact ⟨t, by rw [mul_comm, ht]⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `hS`. Establish `hr : ∀ i j, ∃ t, oToS F E b * (u.1 - 1) i j = (M : Formalism.L2.Herm.intAf F E) * t` using `fun i j => by`. Use `exists_div hIJ hb (mem_idS_prod Pg _ fun PP hP => ?_)` and prove the remaining obligations. Establish `h` using `hx PP hP`. Rewrite `h` using `[redFn_frGL]`.

Establish `h2 : resS F PP (u.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j` using `congrArg (fun g : GL (Fin n) (kP PP) => g.1 i j) h`. Rewrite using `[Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `choose t ht using hr`. Use `set T : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := fun i j => (t i j : E ⊗[F] Formalism.L2.Herm.Af F) with hT`.

Use `set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n u).1 with hY`. Establish `e1 : ((frGL β u : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1` using `rfl`. Establish `e2 : (oToS F E b : E ⊗[F] Formalism.L2.Herm.Af F) • (Y - 1) = M • T`. Use extensionality with `i j`. Establish `e5 : (((u.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j`.

Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Use `congrArg Subtype.val (ht i j)` as an intermediate fact. Rewrite `this` using `[Subring.coe_mul, e5, Subring.coe_mul, Subring.coe_natCast]`. Rewrite using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, this, nsmul_eq_mul]`.

Use `⟨β.1 *ᵥ (T *ᵥ ((β⁻¹).1 *ᵥ z)), (hβ _).2 fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec _ (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mulVec] show ∑ j : Fin n, _ * _ ∈ _`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 ((hβ z).1 hz j)`. Rewrite using `[← Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← e2, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.mulVec_mulVec _ β.1 (β⁻¹).1, Units.mul_inv, Matrix.one_mulVec, e1, ← Matrix.mulVec_mulVec, ← …`.
-/
theorem cong_of_red (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (Pg : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hIJ : (∏ PP ∈ Pg, PP.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β) (hx : ∀ PP ∈ Pg, redFn β PP x = 1)
    {b : 𝓞 E} (hb : b ∈ J) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ ((oToS F E b : E ⊗[F] Formalism.L2.Herm.Af F) • z) - (oToS F E b : E ⊗[F] Formalism.L2.Herm.Af F) • z = M • y := by
  obtain ⟨u, rfl⟩ := hS
  have hr : ∀ i j, ∃ t, oToS F E b * (u.1 - 1) i j = (M : Formalism.L2.Herm.intAf F E) * t := fun i j => by
    refine exists_div hIJ hb (mem_idS_prod Pg _ fun PP hP => ?_)
    have h := hx PP hP
    rw [redFn_frGL] at h
    have h2 : resS F PP (u.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j :=
      congrArg (fun g : GL (Fin n) (kP PP) => g.1 i j) h
    rw [Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose t ht using hr
  set T : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := fun i j => (t i j : E ⊗[F] Formalism.L2.Herm.Af F) with hT
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n u).1 with hY
  have e1 : ((frGL β u : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  have e2 : (oToS F E b : E ⊗[F] Formalism.L2.Herm.Af F) • (Y - 1) = M • T := by
    ext i j
    have e5 : (((u.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    have := congrArg Subtype.val (ht i j)
    rw [Subring.coe_mul, e5, Subring.coe_mul, Subring.coe_natCast] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, this, nsmul_eq_mul]
  refine ⟨β.1 *ᵥ (T *ᵥ ((β⁻¹).1 *ᵥ z)), (hβ _).2 fun i => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec _ (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mulVec]
    show ∑ j : Fin n, _ * _ ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 ((hβ z).1 hz j)
  · rw [← Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← e2, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_smul, ← smul_sub, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec,
      Matrix.mulVec_mulVec _ β.1 (β⁻¹).1, Units.mul_inv, Matrix.one_mulVec, e1, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]

end Frames

section Adelic

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Pj GlobalTheory.Member GlobalTheory.LevSplit
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hg : g ∈ blockTri (κ` using `κ) (blk2 n) := fun i j hij => by`. Simplify using `[blk2] at hij`. Use `upper_block_val_submatrix hr hg` as an intermediate fact. Rewrite `this` using `[h]`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `(congrFun (congrFun this i) j).symm`.
-/
theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) {g : GL (Fin n) κ}
    (h : upperLeftBlock hr g = 1) : g = 1 := by
  subst hn
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := fun i j hij => by
    simp [blk2] at hij
  have := upper_block_val_submatrix hr hg
  rw [h] at this
  apply Units.ext
  ext i j
  exact (congrFun (congrFun this i) j).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `hψ` to reduce the goal to its premises. Establish `e2 : (ψ ∘ fun i => c * z i) = ψ c • fun i => ψ (z i)` using `funext fun i => map_mul _ _ _`. Rewrite using `[Pi.sub_apply, map_sub, Pi.smul_apply, map_nsmul, hy, RingHom.map_mulVec, e2, map_mul]`. Conclude with `congrFun e i`.
-/
theorem transfer_gen {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (hψ : Function.Injective ψ)
    (K : Matrix (Fin n) (Fin n) R) (c : R) (z y' : Fin n → R) (y : Fin n → T) (hy : ∀ i, ψ (y' i) = y i) (M : ℕ)
    (e : K.map ψ *ᵥ (ψ c • fun i => ψ (z i)) - (ψ c • fun i => ψ (z i)) = M • y) :
    K *ᵥ (fun i => c * z i) - (fun i => c * z i) = M • y' := by
  funext i
  apply hψ
  have e2 : (ψ ∘ fun i => c * z i) = ψ c • fun i => ψ (z i) := funext fun i => map_mul _ _ _
  rw [Pi.sub_apply, map_sub, Pi.smul_apply, map_nsmul, hy, RingHom.map_mulVec, e2, map_mul]
  exact congrFun e i

/- English proof (translation)
Rewrite using `[smul_sub, smul_sub, smul_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← e₁, ← e₂, ← e₃, ← e₄, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]`. Normalize the expressions using the abelian group laws.
-/
theorem comb_gen {R : Type} [CommRing R] {n : ℕ} (K K' K'' U : Matrix (Fin n) (Fin n) R) (hU : K * K' * U = K'')
    (M : ℕ) (a a' a'' b w₁ w₂ w₃ w₄ : Fin n → R) (e₁ : a'' - K'' *ᵥ a = M • w₁) (e₂ : b - K *ᵥ a' = M • w₂)
    (e₃ : a' - K' *ᵥ a = M • w₃) (e₄ : U *ᵥ a - a = M • w₄) :
    a'' - b = M • (w₁ + (K * K') *ᵥ w₄ - w₂ - K *ᵥ w₃) := by
  rw [smul_sub, smul_sub, smul_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← e₁, ← e₂, ← e₃, ← e₄,
    Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]
  abel

variable {D : D7}

/- English proof (translation)
Take `⟨c, -, -, -, h1, h2⟩` from `h`. Simplify using `only [one_pow, Nat.cast_one, one_smul] at h1 h2`. Establish `e : (Λ : Set (Fin V.rank → D.host.E)) = latC V`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨_, h2 x hx, ?_⟩` and prove the remaining obligations. Use `show V.frame.equivFun (∑ i, x i • V.frame i) = x`. Rewrite using `[← V.frame.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨v, hv, rfl⟩`.

Use `h1 _ ?_` and prove the remaining obligations. Use `show ∑ i, V.frame.equivFun v i • V.frame i ∈ V.L0`. Rewrite using `[V.frame.sum_equivFun]`. Conclude with `hv`. Rewrite using `[← latHat_iff Λ z, AALev.latHat_eq, e]`.

Both sides reduce to the same expression.
-/
theorem mem_latHat_frame {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ latHat V ↔ (fun i => swp D.host.F D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  have e : (Λ : Set (Fin V.rank → D.host.E)) = latC V := by
    ext x
    constructor
    · intro hx
      refine ⟨_, h2 x hx, ?_⟩
      show V.frame.equivFun (∑ i, x i • V.frame i) = x
      rw [← V.frame.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨v, hv, rfl⟩
      refine h1 _ ?_
      show ∑ i, V.frame.equivFun v i • V.frame i ∈ V.L0
      rw [V.frame.sum_equivFun]
      exact hv
  rw [← latHat_iff Λ z, AALev.latHat_eq, e]
  rfl

/- English proof (translation)
The claim follows from `funext fun i => RingHom.map_mulVec _ _ z i`.
-/
theorem swp_mulVec (V : HSp D) (k : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (fun i => swp D.host.F D.host.E (((finHom V k).1 *ᵥ z) i)) =
      (finE V k).1 *ᵥ fun i => swp D.host.F D.host.E (z i) :=
  funext fun i => RingHom.map_mulVec _ _ z i

/- English proof (translation)
Use `(AALev.congruences_agree D V k).1.2 fun z hz => ⟨_, sub_mem ?_ hz, (one_smul _ _).symm⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[mem_latHat_frame h]`. Rewrite using `[swp_mulVec]`. Conclude with `((mem_St_iff β Λ h.choose_spec.1 _).1 hk).1 _ hz`.
-/
theorem stab_of_St {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : finE V k ∈ St β) : ∀ z ∈ latGHat V 1, (finHom V k).1 *ᵥ z ∈ latGHat V 1 := by
  refine (AALev.congruences_agree D V k).1.2 fun z hz => ⟨_, sub_mem ?_ hz, (one_smul _ _).symm⟩
  rw [mem_latHat_frame h] at hz ⊢
  rw [swp_mulVec]
  exact ((mem_St_iff β Λ h.choose_spec.1 _).1 hk).1 _ hz

/- English proof (translation)
Use `((AALev.congruences_agree D V k).2 M J).1 fun b hb z hz => ?_` and prove the remaining obligations. Rewrite `hz` using `[mem_latHat_frame h]`. Take `⟨y, hy, e⟩` from `cong_of_red β Λ h.choose_spec.1 Pg hIJ _ hk hx hb hz`. Use `choose y' hy' using fun i => (swp_bij (F := D.host.F) (E := D.host.E)).2 (y i)`. Establish `hy2 : y' ∈ latHat V` using `(mem_latHat_frame h _).2 (by rw [funext hy']; exact hy)`.

Conclude with `⟨y', hy2, transfer_gen (swp D.host.F D.host.E) swp_bij.1 (finHom V k).1 ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) z y' y hy' M e⟩`.
-/
theorem cong_of_princ {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) (Pg : Finset (Pl D.host.E))
    {J : Ideal (𝓞 D.host.E)} {M : ℕ} (hIJ : (∏ PP ∈ Pg, PP.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)})
    {k : GA D V} (hk : finE V k ∈ St β) (hx : ∀ PP ∈ Pg, redFn β PP (finE V k) = 1) :
    ∀ a ∈ J • latG V 1, ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  refine ((AALev.congruences_agree D V k).2 M J).1 fun b hb z hz => ?_
  rw [mem_latHat_frame h] at hz
  obtain ⟨y, hy, e⟩ := cong_of_red β Λ h.choose_spec.1 Pg hIJ _ hk hx hb hz
  choose y' hy' using fun i => (swp_bij (F := D.host.F) (E := D.host.E)).2 (y i)
  have hy2 : y' ∈ latHat V := (mem_latHat_frame h _).2 (by rw [funext hy']; exact hy)
  exact ⟨y', hy2, transfer_gen (swp D.host.F D.host.E) swp_bij.1 (finHom V k).1
    ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) z y' y hy' M e⟩

/- English proof (translation)
The claim follows from `funext fun _ => TensorProduct.tmul_sub _ _ _`.
-/
theorem finVec_sub (V : HSp D) (a b : Fin V.rank → D.host.E) : finVec V (a - b) = finVec V a - finVec V b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

/- English proof (translation)
Establish `hM' : (M : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Establish `e2 : finVec V ((M : D.host.E)⁻¹ • ι a) = w`. Use `AALev.fv_smul (F := D.host.F) (M : D.host.E)⁻¹ (ι a)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Establish `e' : GlobalTheory.AdLat.fv D.host.F (ι a) = M • w` using `e`.

Rewrite using `[e', ← Nat.cast_smul_eq_nsmul (GlobalTheory.AdLat.RA D.host.F D.host.E), smul_smul]`. Establish `: (M : GlobalTheory.AdLat.RA D.host.F D.host.E) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (M : D.host.E)` using `(map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := FiniteAdeleRing (𝓞 D.host.F) D.host.F) (B := D.host.E)) M).symm`. Rewrite using `[this, ← AALev.one_tmul_mul, inv_mul_cancel₀ hM', ← Algebra.TensorProduct.one_def, one_smul]`. Establish `hm : (M : D.host.E)⁻¹ • ι a ∈ LinearMap.range ι`. Rewrite using `[hι.2, LatMove.mem_lat_iff, e2]`.

Conclude with `hw`. Take `⟨b, hb⟩` from `hm`. Use `⟨b, hι.1 ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul, hb, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hM', one_smul]`.
-/
theorem exists_div_lat {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : M ≠ 0) {a : La}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) (e : finVec V (ι a) = M • w) :
    ∃ b, a = M • b := by
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have e2 : finVec V ((M : D.host.E)⁻¹ • ι a) = w := by
    have := AALev.fv_smul (F := D.host.F) (M : D.host.E)⁻¹ (ι a)
    refine this.trans ?_
    have e' : GlobalTheory.AdLat.fv D.host.F (ι a) = M • w := e
    rw [e', ← Nat.cast_smul_eq_nsmul (GlobalTheory.AdLat.RA D.host.F D.host.E), smul_smul]
    have : (M : GlobalTheory.AdLat.RA D.host.F D.host.E) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (M : D.host.E) :=
      (map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F)
        (A := FiniteAdeleRing (𝓞 D.host.F) D.host.F) (B := D.host.E)) M).symm
    rw [this, ← AALev.one_tmul_mul, inv_mul_cancel₀ hM', ← Algebra.TensorProduct.one_def, one_smul]
  have hm : (M : D.host.E)⁻¹ • ι a ∈ LinearMap.range ι := by
    rw [hι.2, LatMove.mem_lat_iff, e2]
    exact hw
  obtain ⟨b, hb⟩ := hm
  refine ⟨b, hι.1 ?_⟩
  rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hM', one_smul]

/- English proof (translation)
Use `choose κ hκ hk using hlev`. Establish `hmem : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ι a ∈ J • latG V 1` using `fun a ha => by`. Use `Submodule.mem_map_of_mem (f := ι) ha` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'', Submodule.map_top, hι.2]`. Then use the resulting hypothesis. Establish `triv : ∀ k : GA D V, finE V k ∈ parLev D.sp.cm V.gram β L → rTup β L (finE V k) = 1 → ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V (ι a) - finVec V (ι a) = M • w` using `fun k h1 h2 a ha => cong_of_princ h L.Pg hIJ (parLev_St h1) (fun PP hP => eq_one_of_full_upper_block_eq_one L.hr hL (congrFun h2 ⟨PP, hP⟩)) _ (hmem a ha)`.

Use `⟨fun a ha => ?_, fun g g' a ha => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `hk 1 a ha`. Take `⟨w', hw', e'⟩` from `triv (κ 1) (hκ 1).2.1 ((hκ 1).2.2.trans (map_one eG)) a ha`. Use `exists_div_lat hι hM (add_mem hw hw') ?_` and prove the remaining obligations. Rewrite using `[map_sub, finVec_sub, smul_add, ← e, ← e', sub_add_sub_cancel]`.

Establish `ha' : lev g' a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)`. Use `Submodule.mem_map_of_mem (f := lev g') ha` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top this`. Establish `hp : finE V (κ g * κ g') ∈ parLev D.sp.cm V.gram β L`.

Rewrite using `[map_mul]`. Conclude with `mul_mem (hκ g).2.1 (hκ g').2.1`. Establish `hl : IsLevelLift V β L (eG (g * g')) (κ g * κ g')` using `⟨mul_mem (hκ g).1 (hκ g').1, hp, by`. Rewrite using `[map_mul, rTup_mul (hκ g).2.1 (hκ g').2.1, (hκ g).2.2, (hκ g').2.2, map_mul]⟩`. Establish `hd` using `lift_div_mem hl (hκ (g * g'))`.

Take `⟨w₁, hw₁, e₁⟩` from `hk (g * g') a ha`. Take `⟨w₂, hw₂, e₂⟩` from `hk g _ ha'`. Take `⟨w₃, hw₃, e₃⟩` from `hk g' a ha`. Take `⟨w₄, hw₄, e₄⟩` from `triv _ hd.2.1 hd.2.2 a ha`. Establish `hU : (finHom V (κ g)).1 * (finHom V (κ g')).1 * (finHom V ((κ g * κ g')⁻¹ * κ (g * g'))).1 = (finHom V (κ (g * g'))).1`.

Use `congrArg Units.val (a₁ := finHom V (κ g) * finHom V (κ g') * finHom V ((κ g * κ g')⁻¹ * κ (g * g'))) ?_` and prove the remaining obligations. Rewrite using `[← (finHom V).map_mul, ← (finHom V).map_mul, mul_inv_cancel_left]`. Establish `hw₅` using `stab_of_St h (parLev_St hp) _ hw₄`. Establish `hK : (finHom V (κ g * κ g')).1 = (finHom V (κ g)).1 * (finHom V (κ g')).1` using `congrArg Units.val ((finHom V).map_mul _ _)`. Rewrite `hw₅` using `[hK]`.

Use `exists_div_lat hι hM (sub_mem (sub_mem (add_mem hw₁ hw₅) hw₂) (stab_of_St h (parLev_St (hκ g).2.1) _ hw₃)) ?_` and prove the remaining obligations. Conclude with `((congrArg (finVec V) (ι.map_sub _ _)).trans (finVec_sub V _ _)).trans (comb_gen _ _ _ _ hU M _ _ _ _ _ _ _ _ e₁ e₂ e₃ e₄)`.
-/
theorem mul_on_half {V : HSp D} {β : GL (Fin V.rank) (EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    (L : LevDat D.host.E ℂ V.rank) (hL : V.rank = L.r)
    {J : Ideal (𝓞 D.host.E)} {M : ℕ} (hIJ : (∏ PP ∈ L.Pg, PP.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)})
    (hM : M ≠ 0) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {G : Type} [Group G] (eG : G →* G0 L.Pg L.r)
    (lev : G → La →ₗ[𝓞 D.host.E] La)
    (hlev : ∀ g, ∃ κ, IsLevelLift V β L (eG g) κ ∧
      ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
        finVec V (ι (lev g a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) :
    (∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ b, lev 1 a - a = M • b) ∧
      ∀ g g', ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ b, lev (g * g') a - lev g (lev g' a) = M • b := by
  choose κ hκ hk using hlev
  have hmem : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ι a ∈ J • latG V 1 := fun a ha => by
    have := Submodule.mem_map_of_mem (f := ι) ha
    rwa [Submodule.map_smul'', Submodule.map_top, hι.2] at this
  have triv : ∀ k : GA D V, finE V k ∈ parLev D.sp.cm V.gram β L → rTup β L (finE V k) = 1 →
      ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
        (finHom V k).1 *ᵥ finVec V (ι a) - finVec V (ι a) = M • w := fun k h1 h2 a ha =>
    cong_of_princ h L.Pg hIJ (parLev_St h1) (fun PP hP => eq_one_of_full_upper_block_eq_one L.hr hL (congrFun h2 ⟨PP, hP⟩)) _ (hmem a ha)
  refine ⟨fun a ha => ?_, fun g g' a ha => ?_⟩
  · obtain ⟨w, hw, e⟩ := hk 1 a ha
    obtain ⟨w', hw', e'⟩ := triv (κ 1) (hκ 1).2.1 ((hκ 1).2.2.trans (map_one eG)) a ha
    refine exists_div_lat hι hM (add_mem hw hw') ?_
    rw [map_sub, finVec_sub, smul_add, ← e, ← e', sub_add_sub_cancel]
  · have ha' : lev g' a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La) := by
      have := Submodule.mem_map_of_mem (f := lev g') ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have hp : finE V (κ g * κ g') ∈ parLev D.sp.cm V.gram β L := by
      rw [map_mul]; exact mul_mem (hκ g).2.1 (hκ g').2.1
    have hl : IsLevelLift V β L (eG (g * g')) (κ g * κ g') :=
      ⟨mul_mem (hκ g).1 (hκ g').1, hp, by
        rw [map_mul, rTup_mul (hκ g).2.1 (hκ g').2.1, (hκ g).2.2, (hκ g').2.2, map_mul]⟩
    have hd := lift_div_mem hl (hκ (g * g'))
    obtain ⟨w₁, hw₁, e₁⟩ := hk (g * g') a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hk g _ ha'
    obtain ⟨w₃, hw₃, e₃⟩ := hk g' a ha
    obtain ⟨w₄, hw₄, e₄⟩ := triv _ hd.2.1 hd.2.2 a ha
    have hU : (finHom V (κ g)).1 * (finHom V (κ g')).1 * (finHom V ((κ g * κ g')⁻¹ * κ (g * g'))).1 =
        (finHom V (κ (g * g'))).1 := by
      refine congrArg Units.val (a₁ := finHom V (κ g) * finHom V (κ g') * finHom V ((κ g * κ g')⁻¹ * κ (g * g'))) ?_
      rw [← (finHom V).map_mul, ← (finHom V).map_mul, mul_inv_cancel_left]
    have hw₅ := stab_of_St h (parLev_St hp) _ hw₄
    have hK : (finHom V (κ g * κ g')).1 = (finHom V (κ g)).1 * (finHom V (κ g')).1 :=
      congrArg Units.val ((finHom V).map_mul _ _)
    rw [hK] at hw₅
    refine exists_div_lat hι hM (sub_mem (sub_mem (add_mem hw₁ hw₅) hw₂)
      (stab_of_St h (parLev_St (hκ g).2.1) _ hw₃)) ?_
    exact ((congrArg (finVec V) (ι.map_sub _ _)).trans (finVec_sub V _ _)).trans
      (comb_gen _ _ _ _ hU M _ _ _ _ _ _ _ _ e₁ e₂ e₃ e₄)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem latEmb_cast {V W : HSp D} (e : V = W) {r : ℕ} (hV : V.rank = r) (hW : W.rank = r) {La : Type}
    [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hV) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hW) ∘ₗ ι) := by
  subst e
  exact h

end Adelic

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨t⟩ hO i c' lev hlev`. Establish `hT` using `t.laws`. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q`. Establish `h1` using `(hT.pins.2.2.2 _ hj).1`.

Establish `h2` using `D.R.m_add_three_le_k`. Rewrite using `[h1]`. Simplify using `only [Ranks.sigW]`. Use linear arithmetic over natural numbers and integers. Establish `hA : T.Q.l.A.Coprime T.Q.l.M` using `by rw [hT.pins.2.1.2]; exact Nat.coprime_one_left _`.

Establish `hprod` using `T.Q.l.prod`. Establish `hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal`. Use `GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_` and prove the remaining obligations. Rewrite `hprod` using `[hT.pins.2.1.1]`. Conclude with `(hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left`.

Rewrite using `[hC.lev.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]`. Both sides reduce to the same expression. Establish `hι : LatEmb (Wc D i) (iotaW T i)`. Take `⟨hr, _, _, _, _, _, _, h, _⟩` from `hT.adPin _ hj _ T.good_σ₀`. Conclude with `latEmb_cast (hT.spaceW _ hj _ T.good_σ₀) hr (rank_Wc i) _ h`.

Establish `hM : T.Q.l.M ≠ 0` using `by have := T.Q.l.three_le; omega`. Take `⟨h1, hm⟩` from `mul_on_half (hC.lev.βW i) (R.datWp i R.triv) (rank_Wc i) (J := Mfr T.Q.l) (hMb ▸ hprod) hM hι R.eG.toMonoidHom lev hlev`. Conclude with `actLaws_of_action_mod hpq hA _ c' lev (mem_of_half (lev 1 - LinearMap.id) h1) fun g g' => mem_of_half (lev (g * g') - lev g ∘ₗ lev g') (hm g g')`.
-/
theorem actLev_of_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨t⟩ hO i c' lev hlev
  have hT := t.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (hT.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hA : T.Q.l.A.Coprime T.Q.l.M := by rw [hT.pins.2.1.2]; exact Nat.coprime_one_left _
  have hprod := T.Q.l.prod
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := by
    refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
    · rw [hT.pins.2.1.1] at hprod
      exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
    · rw [hC.lev.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
      rfl
  have hι : LatEmb (Wc D i) (iotaW T i) := by
    obtain ⟨hr, _, _, _, _, _, _, h, _⟩ := hT.adPin _ hj _ T.good_σ₀
    exact latEmb_cast (hT.spaceW _ hj _ T.good_σ₀) hr (rank_Wc i) _ h
  have hM : T.Q.l.M ≠ 0 := by have := T.Q.l.three_le; omega
  obtain ⟨h1, hm⟩ := mul_on_half (hC.lev.βW i) (R.datWp i R.triv) (rank_Wc i) (J := Mfr T.Q.l)
    (hMb ▸ hprod) hM hι R.eG.toMonoidHom lev hlev
  exact actLaws_of_action_mod hpq hA _ c' lev (mem_of_half (lev 1 - LinearMap.id) h1)
    fun g g' => mem_of_half (lev (g * g') - lev g ∘ₗ lev g') (hm g g')

end GlobalTheory.LevelActAnyField
