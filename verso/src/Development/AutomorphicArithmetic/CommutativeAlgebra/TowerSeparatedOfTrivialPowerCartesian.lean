import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Establish `key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x → L.CongOne N (g * x * g⁻¹)`. Introduce `g hg hg' x hx`. Unfold `Link.CongOne at hg hg' hx ⊢`. Introduce `v hv`. Take `⟨w₁, hw₁, h₁⟩` from `hg' v hv`.

Establish `hv₁ : L.actG g⁻¹ v ∈ LaHat D`. Rewrite using `[h₁, one_smul]`. Conclude with `add_mem hv hw₁`. Take `⟨w₂, hw₂, h₂⟩` from `hx _ hv₁`. Take `⟨w₃, hw₃, h₃⟩` from `hg w₂ hw₂`.

Use `⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩` and prove the remaining obligations. Establish `hgg : L.actG g (L.actG g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add, hgg, map_nsmul, h₃, one_smul]`. Establish `hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹` using `hk`.

Establish `hu' : L.CongOne N u ∧ L.CongOne N u⁻¹` using `hu`. Use `show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹`. Use `⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩` and prove the remaining obligations. Establish `hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹` using `by group`. Rewrite using `[hinv]`.

Conclude with `key k hk'.1 hk'.2 u⁻¹ hu'.2`.
-/
private theorem kn_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {k u : G.GAf}
    (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x →
      L.CongOne N (g * x * g⁻¹) := by
    intro g hg hg' x hx
    unfold Link.CongOne at hg hg' hx ⊢
    intro v hv
    obtain ⟨w₁, hw₁, h₁⟩ := hg' v hv
    have hv₁ : L.actG g⁻¹ v ∈ LaHat D := by
      rw [h₁, one_smul]
      exact add_mem hv hw₁
    obtain ⟨w₂, hw₂, h₂⟩ := hx _ hv₁
    obtain ⟨w₃, hw₃, h₃⟩ := hg w₂ hw₂
    refine ⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩
    have hgg : L.actG g (L.actG g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add, hgg, map_nsmul, h₃,
      one_smul]
  have hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹ := hk
  have hu' : L.CongOne N u ∧ L.CongOne N u⁻¹ := hu
  show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹
  refine ⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩
  have hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [hinv]
  exact key k hk'.1 hk'.2 u⁻¹ hu'.2

/- English proof (translation)
Use `haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E`. Express the relevant statement in the definitionally equal form `Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)`. Use `infer_instance`.
-/
private theorem gen_mono {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Mono (gen (Ow w) E) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)
  infer_instance

/- English proof (translation)
Introduce `hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz`. Take `⟨ρ, e, hopen, -, htr⟩` from `hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C`. Establish `hKM` using `T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩`. Use `revert hKM`. Use `revert ρ`.

Generalize the expression as in `T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M`. Introduce `ρ e hopen htr hKM`. Establish `x : (1 : G.GAf) ∈ T.X.Δ` using `T.X.Δ.one_mem`. Establish `y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M` using `fun u hu => by`. Establish `hN : S.N₀ ∣ (N : ℕ)` using `⟨c, hNum.1⟩`.

Establish `hu' : u ∈ L.KN S.N₀` using `KN_anti hN (by rw [← T.K_eq]; exact hu)`. Rewrite using `[hKM]`. Simplify using `using hu'`. Establish `htr'` using `htr x y`. Establish `hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ`.

Rewrite using `[htr', ← Category.assoc, hz, Category.assoc]`. Establish `hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M` using `by haveI : Mono (gen (Ow w) E) := gen_mono w`. Rewrite using `[← cancel_mono (gen (Ow w) E)]`. Simplify using `only [Category.assoc]`. Rewrite using `[← e]`.

Simplify using `only [← Category.assoc] at hzM ⊢`. Rewrite using `[hzM]`. Establish `hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y` using `by haveI := hopen`. Rewrite using `[← cancel_mono (pullback.lift ρ (T.X.q M) e)]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc, pullback.lift_fst]`. Conclude with `hzM`. Simplify using `only [Category.assoc, pullback.lift_snd]`. Conclude with `hzq`. Establish `hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N)`.

Introduce `g hg u hu`. Rewrite `hg` using `[hKM]`. Rewrite `hu`, the goal using `[T.K_eq]`. Conclude with `kn_conj L (KN_anti (one_dvd _) hg) hu`. Take `⟨g, hg, a', b', hz'⟩` from `T.X.trans (T.lev N) M x y hnorm Ω z z' hzt`.

Use `⟨g, ?_, a', b', hz'⟩` and prove the remaining obligations. Rewrite `hg` using `[hKM]`. Take `⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩` from `T.tr_eq N N g a' b'`. Establish `hP2` using `(hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ) (𝟙 _) hw (by simp) k).2.1`. Establish `hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j` using `(hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1`.

Establish `h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom = z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π`. Rewrite using `[hz', Category.assoc, reassoc_of% heq, hP2]`. Establish `h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j = z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j`. Establish `hz2` using `hz`. Unfold `Site.pi at hz2`.

Rewrite using `[← hP3]`. Simplify using `only [← Category.assoc] at hz2 ⊢`. Rewrite using `[hz2]`. Use `hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_` and prove the remaining obligations. Use `show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j = (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j`.

Simplify using `only [Category.assoc]`. Rewrite using `[h2, reassoc_of% h1]`.
-/
theorem UpperTheory.tower_separated_of_trivial_powerCartesian :
    PiZero → BaseSep → PowCart → PiSep := by
  intro hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz
  obtain ⟨ρ, e, hopen, -, htr⟩ := hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  have hKM := T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩
  revert hKM
  revert ρ
  generalize T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M
  intro ρ e hopen htr hKM
  have x : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M := fun u hu => by
    have hN : S.N₀ ∣ (N : ℕ) := ⟨c, hNum.1⟩
    have hu' : u ∈ L.KN S.N₀ := KN_anti hN (by rw [← T.K_eq]; exact hu)
    rw [hKM]
    simpa using hu'
  have htr' := htr x y
  have hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ := by
    rw [htr', ← Category.assoc, hz, Category.assoc]
  have hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M := by
    haveI : Mono (gen (Ow w) E) := gen_mono w
    rw [← cancel_mono (gen (Ow w) E)]
    simp only [Category.assoc]
    rw [← e]
    simp only [← Category.assoc] at hzM ⊢
    rw [hzM]
  have hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y := by
    haveI := hopen
    rw [← cancel_mono (pullback.lift ρ (T.X.q M) e)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hzM
    · simp only [Category.assoc, pullback.lift_snd]
      exact hzq
  have hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N) := by
    intro g hg u hu
    rw [hKM] at hg
    rw [T.K_eq] at hu ⊢
    exact kn_conj L (KN_anti (one_dvd _) hg) hu
  obtain ⟨g, hg, a', b', hz'⟩ := T.X.trans (T.lev N) M x y hnorm Ω z z' hzt
  refine ⟨g, ?_, a', b', hz'⟩
  rw [hKM] at hg
  obtain ⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩ := T.tr_eq N N g a' b'
  have hP2 := (hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ)
    (𝟙 _) hw (by simp) k).2.1
  have hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j :=
    (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1
  have h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom =
      z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π := by
    rw [hz', Category.assoc, reassoc_of% heq, hP2]
  have h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j =
      z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j := by
    have hz2 := hz
    unfold Site.pi at hz2
    rw [← hP3]
    simp only [← Category.assoc] at hz2 ⊢
    rw [hz2]
  refine hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_
  show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j =
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j
  simp only [Category.assoc]
  rw [h2, reassoc_of% h1]
