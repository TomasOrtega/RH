import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `haveI : Module.Projective ℤ Dw.La := by`. Take `⟨s, hs⟩` from `Module.projective_def'.1 Dw.proj`. Use `haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance`. Conclude with `Module.Projective.of_split (s.restrictScalars ℤ) ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ) (LinearMap.ext fun x => LinearMap.congr_fun hs x)`.

Set `f : ℤ →ₗ[ℤ] Additive Fˣ` to `LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)`. Establish `hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f`. Introduce `a`. Establish `h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F`. Rewrite using `[mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]`.

Both sides reduce to the same expression. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_mem_rootsOfUnity h1`. Use `⟨i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(i : ℤ) • Additive.ofMul ζ = φ a`. Rewrite using `[natCast_zsmul, ← ofMul_pow, hi]`.

Both sides reduce to the same expression. Take `⟨ψ, hψ⟩` from `Module.projective_lifting_property f.rangeRestrict (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict`. Take `⟨d, hd⟩` from `Dw.unimod.2 ψ`. Use `⟨-d, fun a => ?_⟩` and prove the remaining obligations. Establish `skew : Dw.EF a (-d) = ψ a`.

Use `Dw.alt (d + a)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, Dw.alt] at this`. Rewrite using `[map_neg, ← hd]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : f (ψ a) = φ a` using `congrArg Subtype.val (LinearMap.congr_fun hψ a)`.

Rewrite using `[skew, ← h2]`. Both sides reduce to the same expression.
-/
theorem datum_character_eq_zpow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    {F : Type} [Field F] {M : ℕ} (hM : 0 < M) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M)
    (φ : Dw.La →+ Additive Fˣ) (hφ : ∀ a, φ (M • a) = 0) :
    ∃ d : Dw.La, ∀ a, Additive.toMul (φ a) = ζ ^ Dw.EF a d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hs x)
  let f : ℤ →ₗ[ℤ] Additive Fˣ := LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)
  have hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f := by
    intro a
    have h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F := by
      rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]; rfl
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    refine ⟨i, ?_⟩
    change (i : ℤ) • Additive.ofMul ζ = φ a
    rw [natCast_zsmul, ← ofMul_pow, hi]; rfl
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f.rangeRestrict
    (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict
  obtain ⟨d, hd⟩ := Dw.unimod.2 ψ
  refine ⟨-d, fun a => ?_⟩
  have skew : Dw.EF a (-d) = ψ a := by
    have := Dw.alt (d + a)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at this
    rw [map_neg, ← hd]
    linarith
  have h2 : f (ψ a) = φ a := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [skew, ← h2]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H R _ _ F _ _ A`. Set `_` to `H.starRing`. Introduce `oA Dw I N k hN hk hco β u u' hβ huu κ hκ`. Establish `hM : 0 < k * N` using `Nat.mul_pos hk hN`. Establish `hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c` using `fun c b => I.lin _ c b`.

Take `⟨t, k', htk⟩` from `(Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))`. Simplify using `only [eq_intCast, Int.cast_natCast] at htk`. Choose the witnesses or unpack the hypotheses as in `⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by`. Use `⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[← hβ]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(-(k * k' : 𝓞 E)) * huu - htk - t * hβ`. Establish `hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1`. Introduce `c a`.

Rewrite using `[mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `(I.ker _ hM _).2 ⟨_, rfl⟩`. Establish `hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1`. Introduce `a`. Rewrite using `[← hlin, smul_smul, hw, hzero]`.

Establish `hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a`. Introduce `a ha`. Take `⟨f, hf⟩` from `(I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)`. Establish `h1 : a = ε • a + (k * N) • (v • f)`. Rewrite using `[smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]`.

Use `conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]`. Set `φ : Dw.La →+ Additive Fˣ` to `AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a)))) (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])`. Establish `hφ : ∀ a, φ ((k * N) • a) = 0`. Introduce `a`. Rewrite using `[← map_zero φ]`.

Express the relevant statement in the definitionally equal form `Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))`. Rewrite using `[smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero, (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]`. Take `⟨d, hd⟩` from `datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ`. Use `⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← hlin, smul_smul]`.

Express the relevant statement in the definitionally equal form `I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1`. Rewrite using `[← map_mul, hw, map_mul, map_natCast, hzero]`. Establish `hzN : z ^ N = 1` using `pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz`. Take `⟨a, rfl⟩` from `(I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])`. Establish `h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d)`.

Rewrite using `[← Dw.adj, ← hd]`. Express the relevant statement in the definitionally equal form `_ = κ (I.ev (k * N) (ε • ε • a))`. Rewrite using `[hfix _ (hkill a), hfix a hz]`. Rewrite using `[h1]`. Conclude with `I.isom _ hM _ _`.
-/
theorem character_eq_weil_pairing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] (A : PolAV (Sp (FractionRing R))), letI := H.starRing; ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a) (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N k : ℕ), 1 ≤ N → 1 ≤ k → Nat.Coprime N k → ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 → ∀ κ : (TFK (R := R) F ⟶ A.A) → Fˣ, (∀ z z', z ≫ oA.act β = 1 → z' ≫ oA.act β = 1 → κ (z * z') = κ z * κ z') → ∃ b : TFK (R := R) F ⟶ A.A, b ≫ oA.act (star β) = 1 ∧ ∀ z, z ≫ oA.act β = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z b (unitOn (κ z)) := by
  intro E _ _ _ H R _ _ F _ _ A
  let _ := H.starRing
  intro oA Dw I N k hN hk hco β u u' hβ huu κ hκ
  have hM : 0 < k * N := Nat.mul_pos hk hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c := fun c b => I.lin _ c b
  obtain ⟨t, k', htk⟩ := (Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at htk
  obtain ⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by
    refine ⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩
    · push_cast
      rw [← hβ]; ring
    · linear_combination (-(k * k' : 𝓞 E)) * huu - htk - t * hβ
  have hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1 := by
    intro c a
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact (I.ker _ hM _).2 ⟨_, rfl⟩
  have hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1 := by
    intro a
    rw [← hlin, smul_smul, hw, hzero]
  have hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a := by
    intro a ha
    obtain ⟨f, hf⟩ := (I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)
    have h1 : a = ε • a + (k * N) • (v • f) := by
      rw [smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]
    conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]
  let φ : Dw.La →+ Additive Fˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a))))
    (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])
  have hφ : ∀ a, φ ((k * N) • a) = 0 := by
    intro a
    rw [← map_zero φ]
    change Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))
    rw [smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero,
      (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]
  obtain ⟨d, hd⟩ := datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ
  refine ⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩
  · rw [← hlin, smul_smul]
    change I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1
    rw [← map_mul, hw, map_mul, map_natCast, hzero]
  · have hzN : z ^ N = 1 := pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz
    obtain ⟨a, rfl⟩ := (I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])
    have h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d) := by
      rw [← Dw.adj, ← hd]
      change _ = κ (I.ev (k * N) (ε • ε • a))
      rw [hfix _ (hkill a), hfix a hz]
    rw [h1]
    exact I.isom _ hM _ _

end GlobalTheory
