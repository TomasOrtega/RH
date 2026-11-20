import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.Auxfm

section
variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨c, hc⟩` from `h (L.cls y hy)`. Take `⟨x, hx, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K q).1 c`. Establish `hb : L.d q (φ.f q x) = 0` using `by rw [φ.comm, hx, map_zero]`. Establish `hsy : L.d q (s • y) = 0` using `by rw [map_smul, hy, smul_zero]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Rewrite `hc` using `[CrystallineSemistableComparison.P.mapH_cls φ q x hx hb, ← (CrystallineSemistableComparison.P.cls_surj L q).2.2.2.2 s y hy hsy]`. Conclude with `((CrystallineSemistableComparison.P.cls_surj L q).2.2.1 _ _ hb hsy).1 hc`.
-/
theorem surj_get {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (s : R) (q : ℕ)
    (h : SurjUpTo s (φ.mapH q)) (y : L.X q) (hy : L.d q y = 0) :
    ∃ x, K.d q x = 0 ∧ φ.f q x - s • y ∈ L.B q := by
  obtain ⟨c, hc⟩ := h (L.cls y hy)
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K q).1 c
  have hb : L.d q (φ.f q x) = 0 := by rw [φ.comm, hx, map_zero]
  have hsy : L.d q (s • y) = 0 := by rw [map_smul, hy, smul_zero]
  refine ⟨x, hx, ?_⟩
  rw [CrystallineSemistableComparison.P.mapH_cls φ q x hx hb, ← (CrystallineSemistableComparison.P.cls_surj L q).2.2.2.2 s y hy hsy] at hc
  exact ((CrystallineSemistableComparison.P.cls_surj L q).2.2.1 _ _ hb hsy).1 hc

/- English proof (translation)
Establish `hb' : L.d q (φ.f q x) = 0` using `by rw [φ.comm, hx, map_zero]`. Establish `h0 : φ.mapH q (K.cls x hx) = 0`. Rewrite using `[CrystallineSemistableComparison.P.mapH_cls φ q x hx hb']`. Conclude with `((CrystallineSemistableComparison.P.cls_surj L q).2.1 _ hb').2 hb`. Establish `hsx : K.d q (s • x) = 0` using `by rw [map_smul, hx, smul_zero]`.

Use `h _ h0` as an intermediate fact. Rewrite `this` using `[← (CrystallineSemistableComparison.P.cls_surj K q).2.2.2.2 s x hx hsx]`. Conclude with `((CrystallineSemistableComparison.P.cls_surj K q).2.1 _ hsx).1 this`.
-/
theorem inj_get {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (s : R) (q : ℕ)
    (h : InjUpTo s (φ.mapH q)) (x : K.X q) (hx : K.d q x = 0) (hb : φ.f q x ∈ L.B q) :
    s • x ∈ K.B q := by
  have hb' : L.d q (φ.f q x) = 0 := by rw [φ.comm, hx, map_zero]
  have h0 : φ.mapH q (K.cls x hx) = 0 := by
    rw [CrystallineSemistableComparison.P.mapH_cls φ q x hx hb']; exact ((CrystallineSemistableComparison.P.cls_surj L q).2.1 _ hb').2 hb
  have hsx : K.d q (s • x) = 0 := by rw [map_smul, hx, smul_zero]
  have := h _ h0
  rw [← (CrystallineSemistableComparison.P.cls_surj K q).2.2.2.2 s x hx hsx] at this
  exact ((CrystallineSemistableComparison.P.cls_surj K q).2.1 _ hsx).1 this

/- English proof (translation)
Introduce `c`. Take `⟨y, hy, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj L n).1 c`. Take `⟨x, hx, hm⟩` from `h y hy`. Establish `hb : L.d n (φ.f n x) = 0` using `by rw [φ.comm, hx, map_zero]`. Establish `hsy : L.d n (s • y) = 0` using `by rw [map_smul, hy, smul_zero]`.

Use `⟨K.cls x hx, ?_⟩` and prove the remaining obligations. Rewrite using `[CrystallineSemistableComparison.P.mapH_cls φ n x hx hb, ← (CrystallineSemistableComparison.P.cls_surj L n).2.2.2.2 s y hy hsy]`. Conclude with `((CrystallineSemistableComparison.P.cls_surj L n).2.2.1 _ _ hb hsy).2 hm`.
-/
theorem surj_mk {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (s : R) (n : ℕ)
    (h : ∀ y : L.X n, L.d n y = 0 → ∃ x, K.d n x = 0 ∧ φ.f n x - s • y ∈ L.B n) : SurjUpTo s (φ.mapH n) := by
  intro c
  obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L n).1 c
  obtain ⟨x, hx, hm⟩ := h y hy
  have hb : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have hsy : L.d n (s • y) = 0 := by rw [map_smul, hy, smul_zero]
  refine ⟨K.cls x hx, ?_⟩
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx hb, ← (CrystallineSemistableComparison.P.cls_surj L n).2.2.2.2 s y hy hsy]
  exact ((CrystallineSemistableComparison.P.cls_surj L n).2.2.1 _ _ hb hsy).2 hm

/- English proof (translation)
Introduce `c hc`. Take `⟨x, hx, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K n).1 c`. Establish `hb : L.d n (φ.f n x) = 0` using `by rw [φ.comm, hx, map_zero]`. Establish `hsx : K.d n (s • x) = 0` using `by rw [map_smul, hx, smul_zero]`. Rewrite `hc` using `[CrystallineSemistableComparison.P.mapH_cls φ n x hx hb]`.

Rewrite using `[← (CrystallineSemistableComparison.P.cls_surj K n).2.2.2.2 s x hx hsx]`. Conclude with `((CrystallineSemistableComparison.P.cls_surj K n).2.1 _ hsx).2 (h x hx (((CrystallineSemistableComparison.P.cls_surj L n).2.1 _ hb).1 hc))`.
-/
theorem inj_mk {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (s : R) (n : ℕ)
    (h : ∀ x : K.X n, K.d n x = 0 → φ.f n x ∈ L.B n → s • x ∈ K.B n) : InjUpTo s (φ.mapH n) := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 c
  have hb : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have hsx : K.d n (s • x) = 0 := by rw [map_smul, hx, smul_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx hb] at hc
  rw [← (CrystallineSemistableComparison.P.cls_surj K n).2.2.2.2 s x hx hsx]
  exact ((CrystallineSemistableComparison.P.cls_surj K n).2.1 _ hsx).2 (h x hx (((CrystallineSemistableComparison.P.cls_surj L n).2.1 _ hb).1 hc))

/- English proof (translation)
Rewrite using `[smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]`.
-/
theorem unsign {M : Type*} [AddCommGroup M] (k : ℕ) (v : M) : (-1 : ℤ) ^ k • (-1 : ℤ) ^ k • v = v := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/- English proof (translation)
Rewrite using `[← unsign k v, h, smul_zero]`.
-/
theorem sign_eq_zero {M : Type*} [AddCommGroup M] {k : ℕ} {v : M} (h : (-1 : ℤ) ^ k • v = 0) : v = 0 := by
  rw [← unsign k v, h, smul_zero]

variable (K : DCx.{w} R)

def Sup (k : ℕ) (x : ∀ p q, K.X p q) : Prop := ∀ p q, p < k → x p q = 0

def Bf : ℕ → Submodule R (∀ p q, K.X p q)
  | 0 => ⊥
  | n + 1 => (K.T n).map K.D

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => rw [(Submodule.mem_bot R).1 hw, map_zero]`. Consider the case `succ n => obtain ⟨z, -, rfl⟩ := hw`. Conclude with `K.DD z`.
-/
theorem D_Bf {n : ℕ} {w : ∀ p q, K.X p q} (hw : w ∈ Bf K n) : K.D w = 0 := by
  cases n with
  | zero => rw [(Submodule.mem_bot R).1 hw, map_zero]
  | succ n => obtain ⟨z, -, rfl⟩ := hw; exact K.DD z

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => rw [(Submodule.mem_bot R).1 hw]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ n => obtain ⟨z, hz, rfl⟩ := hw`. Conclude with `K.D_mem n z hz`.
-/
theorem Bf_le {n : ℕ} {w : ∀ p q, K.X p q} (hw : w ∈ Bf K n) : w ∈ K.T n := by
  cases n with
  | zero => rw [(Submodule.mem_bot R).1 hw]; exact Submodule.zero_mem _
  | succ n => obtain ⟨z, hz, rfl⟩ := hw; exact K.D_mem n z hz

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `x ∈ (⊥ : Submodule R _) ↔ x.1 ∈ (⊥ : Submodule R _)`. Simplify using `only [Submodule.mem_bot]`. Conclude with `⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩`.

Consider the case `succ n`. Express the relevant statement in the definitionally equal form `x ∈ LinearMap.range _ ↔ x.1 ∈ (K.T n).map K.D`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z.1, z.2, rfl⟩`.

Introduce and unpack `⟨z, hz, e⟩`. Conclude with `⟨⟨z, hz⟩, Subtype.ext e⟩`.
-/
theorem tot_B {n : ℕ} (x : K.tot.X n) : x ∈ K.tot.B n ↔ x.1 ∈ Bf K n := by
  cases n with
  | zero =>
    change x ∈ (⊥ : Submodule R _) ↔ x.1 ∈ (⊥ : Submodule R _)
    simp only [Submodule.mem_bot]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | succ n =>
    change x ∈ LinearMap.range _ ↔ x.1 ∈ (K.T n).map K.D
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨z.1, z.2, rfl⟩
    · rintro ⟨z, hz, e⟩; exact ⟨⟨z, hz⟩, Subtype.ext e⟩

/- English proof (translation)
Rewrite using `[K.D_apply]`. Establish `h1 : K.Dh x k (q + 1) = 0`. Break down `k with _ | k` into its components or cases. Both sides reduce to the same expression. Use `show K.dh k (q + 1) (x k (q + 1)) = 0; rw [hx k (q + 1) (by omega), map_zero]`.

Rewrite using `[h1, zero_add]`. Both sides reduce to the same expression.
-/
theorem D_at {k : ℕ} {x : ∀ p q, K.X p q} (hx : Sup K k x) (q : ℕ) :
    K.D x k (q + 1) = (-1 : ℤ) ^ k • K.dv k q (x k q) := by
  rw [K.D_apply]
  have h1 : K.Dh x k (q + 1) = 0 := by
    rcases k with _ | k
    · rfl
    · show K.dh k (q + 1) (x k (q + 1)) = 0; rw [hx k (q + 1) (by omega), map_zero]
  rw [h1, zero_add]; rfl

/- English proof (translation)
Introduce `a b hab` and use `K.sgl_ne c (by omega)`.
-/
theorem sgl_mem {p q n : ℕ} (h : p + q = n) (c : K.X p q) : K.sgl p q c ∈ K.T n :=
  fun a b hab => K.sgl_ne c (by omega)

variable {K} {L : DCx.{w'} R}

def Φ (φ : DCx.Hom K L (RingHom.id R)) : (∀ p q, K.X p q) →ₗ[R] (∀ p q, L.X p q) where
  toFun x p q := φ.f p q (x p q)
  map_add' x y := by funext p q; exact map_add _ _ _
  map_smul' r x := by funext p q; exact map_smul _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Φ_apply (φ : DCx.Hom K L (RingHom.id R)) (x : ∀ p q, K.X p q) (p q : ℕ) : Φ φ x p q = φ.f p q (x p q) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `p q`. Express the relevant statement in the definitionally equal form `φ.f p q (K.D x p q) = L.D (fun p q => φ.f p q (x p q)) p q`. Apply the tactic sequence `rcases p with _ | p <;> rcases q with _ | q <;> simp [DCx.D_apply, DCx.Dh, DCx.Dv, φ.ch, φ.cv]`.
-/
theorem Φ_D (φ : DCx.Hom K L (RingHom.id R)) (x : ∀ p q, K.X p q) : Φ φ (K.D x) = L.D (Φ φ x) := by
  funext p q
  change φ.f p q (K.D x p q) = L.D (fun p q => φ.f p q (x p q)) p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [DCx.D_apply, DCx.Dh, DCx.Dv, φ.ch, φ.cv]

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Express the relevant statement in the definitionally equal form `φ.f a b (K.sgl p q c a b) = _`. Distinguish the cases in `h : a = p ∧ b = q`. Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[K.sgl_self, L.sgl_self]`.

Rewrite using `[K.sgl_ne _ (not_and_or.mp h), L.sgl_ne _ (not_and_or.mp h), map_zero]`.
-/
theorem Φ_sgl (φ : DCx.Hom K L (RingHom.id R)) (p q : ℕ) (c : K.X p q) : Φ φ (K.sgl p q c) = L.sgl p q (φ.f p q c) := by
  funext a b
  change φ.f a b (K.sgl p q c a b) = _
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h; rw [K.sgl_self, L.sgl_self]
  · rw [K.sgl_ne _ (not_and_or.mp h), L.sgl_ne _ (not_and_or.mp h), map_zero]

/- English proof (translation)
Introduce `p q h`. Express the relevant statement in the definitionally equal form `φ.f p q (x p q) = 0`. Rewrite using `[hx p q h, map_zero]`.
-/
theorem doubleComplexMap_mem_total (φ : DCx.Hom K L (RingHom.id R)) {n : ℕ} {x : ∀ p q, K.X p q} (hx : x ∈ K.T n) : Φ φ x ∈ L.T n := by
  intro p q h; change φ.f p q (x p q) = 0; rw [hx p q h, map_zero]

/- English proof (translation)
Consider the cases of `q with`. Consider the case `zero`. Establish `: v = 0` using `(Submodule.mem_bot R).1 hv`. Use `⟨0, Submodule.zero_mem _, fun p' q' _ => ?_⟩` and prove the remaining obligations. Rewrite using `[this, map_zero]`.

Consider the case `succ q`. Take `⟨u, rfl⟩` from `hv`. Use `⟨L.D ((-1 : ℤ) ^ k • L.sgl k q u), ?_, fun p' q' hp => ?_⟩` and prove the remaining obligations. Use `show _ ∈ (L.T (k + q)).map L.D`. Conclude with `⟨_, zsmul_mem (sgl_mem L rfl u) _, rfl⟩`.

Rewrite using `[map_zsmul, L.D_sgl, smul_add, unsign, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, L.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]`.
-/
theorem colB {k q : ℕ} (v : L.X k q) (hv : v ∈ (L.col k).B q) :
    ∃ w ∈ Bf L (k + q), ∀ p' q', p' ≤ k → w p' q' = L.sgl k q v p' q' := by
  cases q with
  | zero =>
    have : v = 0 := (Submodule.mem_bot R).1 hv
    refine ⟨0, Submodule.zero_mem _, fun p' q' _ => ?_⟩
    rw [this, map_zero]
  | succ q =>
    obtain ⟨u, rfl⟩ := hv
    refine ⟨L.D ((-1 : ℤ) ^ k • L.sgl k q u), ?_, fun p' q' hp => ?_⟩
    · show _ ∈ (L.T (k + q)).map L.D
      exact ⟨_, zsmul_mem (sgl_mem L rfl u) _, rfl⟩
    · rw [map_zsmul, L.D_sgl, smul_add, unsign, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        L.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]

/- English proof (translation)
Rewrite using `[map_sub, map_sub, map_smul, hDy, D_Bf L hw, Φ_D]`. Simplify using the standard rewrite rules.
-/
theorem D_res (φ : DCx.Hom K L (RingHom.id R)) {n : ℕ} (y : ∀ p q, L.X p q) (hDy : L.D y = 0) (m : R)
    (a : ∀ p q, K.X p q) {w : ∀ p q, L.X p q} (hw : w ∈ Bf L n) :
    L.D (m • y - Φ φ a - w) = - Φ φ (K.D a) := by
  rw [map_sub, map_sub, map_smul, hDy, D_Bf L hw, Φ_D]; simp

end
end CrystallineSemistableComparison.Auxfm

namespace CrystallineSemistableComparison.Auxfm
section
variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R}

/- English proof (translation)
Use `set r := s ^ (2 * k) • y - Φ φ a - w with hr_def`. Establish `hDr : L.D r = - Φ φ (K.D a)` using `D_res φ y hDy _ a hw`. Establish `hbc : K.dv k (q + 1) (K.D a k (q + 1)) = 0`. Establish `h` using `congrFun (congrFun (K.DD a) k) (q + 1 + 1)`. Rewrite `h` using `[D_at K hb (q + 1)]`.

Conclude with `sign_eq_zero h`. Establish `hφb : (φ.col k).f (q + 1) (K.D a k (q + 1)) ∈ (L.col k).B (q + 1)`. Use `⟨-((-1 : ℤ) ^ k • r k q), ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hDr k) (q + 1)`. Rewrite `h` using `[D_at L hr q]`.

Express the relevant statement in the definitionally equal form `L.dv k q (-((-1 : ℤ) ^ k • r k q)) = φ.f k (q + 1) (K.D a k (q + 1))`. Rewrite using `[map_neg, map_zsmul, h, Pi.neg_apply, Pi.neg_apply, neg_neg]`. Both sides reduce to the same expression. Take `⟨c, hc⟩` from `inj_get (φ.col k) s (q + 1) hI _ hbc hφb`. Express the relevant statement in the definitionally equal form `K.dv k q c = s • K.D a k (q + 1) at hc`.

Establish `hDaT : K.D a ∈ K.T (k + q + 1)` using `K.D_mem _ a ha`. Establish `ha'T : s • a - (-1 : ℤ) ^ k • K.sgl k q c ∈ K.T (k + q)` using `sub_mem (Submodule.smul_mem _ _ ha) (zsmul_mem (sgl_mem K rfl c) _)`. Use `set a' := s • a - (-1 : ℤ) ^ k • K.sgl k q c with ha'`. Establish `hb' : Sup K (k + 1) (K.D a')`. Introduce `p' q' hp`.

Rewrite using `[ha', map_sub, map_smul, map_zsmul, K.D_sgl, smul_add, unsign]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]`. Rewrite using `[K.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp` into its components or cases. Rewrite using `[hb p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]`.

Substitute `hp` using the available equality. Distinguish the cases in `hq : q' = q + 1`. Substitute `hq` using the available equality. Rewrite using `[K.sgl_self, ← hc, sub_self]`. Rewrite using `[hDaT _ q' (by omega), K.sgl_ne _ (Or.inr hq), smul_zero, sub_zero]`.

Establish `hDr' : L.D (s ^ (2 * k + 1) • y - Φ φ a' - s • w) = - Φ φ (K.D a')` using `D_res φ y hDy _ a' (Submodule.smul_mem _ s hw)`. Establish `e1 : s ^ (2 * k + 1) • y - Φ φ a' - s • w = s • r + (-1 : ℤ) ^ k • L.sgl k q (φ.f k q c)`. Rewrite using `[hr_def, ha', map_sub, map_smul, map_zsmul, Φ_sgl, pow_succ s (2 * k), mul_smul, smul_comm (s ^ (2 * k)) s y, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hr'T : s ^ (2 * k + 1) • y - Φ φ a' - s • w ∈ L.T (k + q)` using `sub_mem (sub_mem (Submodule.smul_mem _ _ hy) (doubleComplexMap_mem_total φ ha'T)) (Submodule.smul_mem _ _ (Bf_le L hw))`.

Use `set r' := s ^ (2 * k + 1) • y - Φ φ a' - s • w with hr'_def`. Establish `hr'k : Sup L k r'`. Introduce `p' q' hp`. Rewrite using `[e1]`. Simplify using `only [Pi.add_apply, Pi.smul_apply]`.

Rewrite using `[hr p' q' hp, L.sgl_ne _ (Or.inl (by omega)), smul_zero, smul_zero, add_zero]`. Establish `hr'c : L.dv k q (r' k q) = 0`. Establish `h` using `congrFun (congrFun hDr' k) (q + 1)`. Rewrite `h` using `[D_at L hr'k q, Pi.neg_apply, Pi.neg_apply, Φ_apply, hb' k (q + 1) (by omega), map_zero, neg_zero]`. Conclude with `sign_eq_zero h`.

Take `⟨c', hc'0, hc'⟩` from `surj_get (φ.col k) s q hS (r' k q) hr'c`. Express the relevant statement in the definitionally equal form `K.dv k q c' = 0 at hc'0`. Express the relevant statement in the definitionally equal form `φ.f k q c' - s • r' k q ∈ _ at hc'`. Take `⟨w₀, hw₀, hw₀e⟩` from `colB _ hc'`. Use `⟨s • a' + K.sgl k q c', add_mem (Submodule.smul_mem _ _ ha'T) (sgl_mem K rfl c'), s • (s • w) - w₀, sub_mem (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw)) hw₀, ?_, ?_⟩` and prove the remaining obligations.

Establish `e2 : s ^ (2 * (k + 1)) • y - Φ φ (s • a' + K.sgl k q c') - (s • (s • w) - w₀) = s • r' - L.sgl k q (φ.f k q c') + w₀`. Rewrite using `[hr'_def, map_add, map_smul, Φ_sgl, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ s (2 * k + 1), mul_smul, smul_comm (s ^ (2 * k + 1)) s y, smul_sub, smul_sub]; abel`. Rewrite using `[e2]`. Introduce `p' q' hp`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]`.

Rewrite using `[hw₀e p' q' (by omega)]`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp` into its components or cases. Rewrite using `[hr'k p' q' hp, L.sgl_ne _ (Or.inl (by omega)), L.sgl_ne _ (Or.inl (by omega))]; simp`. Substitute `hp` using the available equality. Distinguish the cases in `hq : q' = q`.

Substitute `hq` using the available equality. Rewrite using `[L.sgl_self, L.sgl_self]`. Normalize the expressions using the abelian group laws. Rewrite using `[hr'T _ q' (by omega), L.sgl_ne _ (Or.inr hq), L.sgl_ne _ (Or.inr hq)]; simp`. Introduce `p' q' hp`.

Rewrite using `[map_add, map_smul, K.D_sgl, hc'0, map_zero, smul_zero, add_zero]`. Simplify using `only [Pi.add_apply, Pi.smul_apply]`. Rewrite using `[hb' p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, add_zero]`.
-/
theorem surj_step (φ : DCx.Hom K L (RingHom.id R)) (s : R) (k q : ℕ)
    (hS : SurjUpTo s ((φ.col k).mapH q)) (hI : InjUpTo s ((φ.col k).mapH (q + 1)))
    (y : ∀ p q, L.X p q) (hy : y ∈ L.T (k + q)) (hDy : L.D y = 0)
    (a : ∀ p q, K.X p q) (ha : a ∈ K.T (k + q)) (w : ∀ p q, L.X p q) (hw : w ∈ Bf L (k + q))
    (hr : Sup L k (s ^ (2 * k) • y - Φ φ a - w)) (hb : Sup K k (K.D a)) :
    ∃ a ∈ K.T (k + q), ∃ w ∈ Bf L (k + q),
      Sup L (k + 1) (s ^ (2 * (k + 1)) • y - Φ φ a - w) ∧ Sup K (k + 1) (K.D a) := by
  set r := s ^ (2 * k) • y - Φ φ a - w with hr_def
  have hDr : L.D r = - Φ φ (K.D a) := D_res φ y hDy _ a hw
  have hbc : K.dv k (q + 1) (K.D a k (q + 1)) = 0 := by
    have h := congrFun (congrFun (K.DD a) k) (q + 1 + 1)
    rw [D_at K hb (q + 1)] at h
    exact sign_eq_zero h
  have hφb : (φ.col k).f (q + 1) (K.D a k (q + 1)) ∈ (L.col k).B (q + 1) := by
    refine ⟨-((-1 : ℤ) ^ k • r k q), ?_⟩
    have h := congrFun (congrFun hDr k) (q + 1)
    rw [D_at L hr q] at h
    change L.dv k q (-((-1 : ℤ) ^ k • r k q)) = φ.f k (q + 1) (K.D a k (q + 1))
    rw [map_neg, map_zsmul, h, Pi.neg_apply, Pi.neg_apply, neg_neg]; rfl
  obtain ⟨c, hc⟩ := inj_get (φ.col k) s (q + 1) hI _ hbc hφb
  change K.dv k q c = s • K.D a k (q + 1) at hc
  have hDaT : K.D a ∈ K.T (k + q + 1) := K.D_mem _ a ha
  have ha'T : s • a - (-1 : ℤ) ^ k • K.sgl k q c ∈ K.T (k + q) :=
    sub_mem (Submodule.smul_mem _ _ ha) (zsmul_mem (sgl_mem K rfl c) _)
  set a' := s • a - (-1 : ℤ) ^ k • K.sgl k q c with ha'
  have hb' : Sup K (k + 1) (K.D a') := by
    intro p' q' hp
    rw [ha', map_sub, map_smul, map_zsmul, K.D_sgl, smul_add, unsign]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
    rw [K.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · rw [hb p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
    · subst hp
      by_cases hq : q' = q + 1
      · subst hq; rw [K.sgl_self, ← hc, sub_self]
      · rw [hDaT _ q' (by omega), K.sgl_ne _ (Or.inr hq), smul_zero, sub_zero]
  have hDr' : L.D (s ^ (2 * k + 1) • y - Φ φ a' - s • w) = - Φ φ (K.D a') :=
    D_res φ y hDy _ a' (Submodule.smul_mem _ s hw)
  have e1 : s ^ (2 * k + 1) • y - Φ φ a' - s • w = s • r + (-1 : ℤ) ^ k • L.sgl k q (φ.f k q c) := by
    rw [hr_def, ha', map_sub, map_smul, map_zsmul, Φ_sgl, pow_succ s (2 * k), mul_smul,
      smul_comm (s ^ (2 * k)) s y, smul_sub, smul_sub]; abel
  have hr'T : s ^ (2 * k + 1) • y - Φ φ a' - s • w ∈ L.T (k + q) :=
    sub_mem (sub_mem (Submodule.smul_mem _ _ hy) (doubleComplexMap_mem_total φ ha'T)) (Submodule.smul_mem _ _ (Bf_le L hw))
  set r' := s ^ (2 * k + 1) • y - Φ φ a' - s • w with hr'_def
  have hr'k : Sup L k r' := by
    intro p' q' hp
    rw [e1]; simp only [Pi.add_apply, Pi.smul_apply]
    rw [hr p' q' hp, L.sgl_ne _ (Or.inl (by omega)), smul_zero, smul_zero, add_zero]
  have hr'c : L.dv k q (r' k q) = 0 := by
    have h := congrFun (congrFun hDr' k) (q + 1)
    rw [D_at L hr'k q, Pi.neg_apply, Pi.neg_apply, Φ_apply, hb' k (q + 1) (by omega), map_zero, neg_zero] at h
    exact sign_eq_zero h
  obtain ⟨c', hc'0, hc'⟩ := surj_get (φ.col k) s q hS (r' k q) hr'c
  change K.dv k q c' = 0 at hc'0
  change φ.f k q c' - s • r' k q ∈ _ at hc'
  obtain ⟨w₀, hw₀, hw₀e⟩ := colB _ hc'
  refine ⟨s • a' + K.sgl k q c', add_mem (Submodule.smul_mem _ _ ha'T) (sgl_mem K rfl c'),
    s • (s • w) - w₀, sub_mem (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw)) hw₀, ?_, ?_⟩
  · have e2 : s ^ (2 * (k + 1)) • y - Φ φ (s • a' + K.sgl k q c') - (s • (s • w) - w₀) =
        s • r' - L.sgl k q (φ.f k q c') + w₀ := by
      rw [hr'_def, map_add, map_smul, Φ_sgl, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ s (2 * k + 1),
        mul_smul, smul_comm (s ^ (2 * k + 1)) s y, smul_sub, smul_sub]; abel
    rw [e2]
    intro p' q' hp
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [hw₀e p' q' (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · rw [hr'k p' q' hp, L.sgl_ne _ (Or.inl (by omega)), L.sgl_ne _ (Or.inl (by omega))]; simp
    · subst hp
      by_cases hq : q' = q
      · subst hq; rw [L.sgl_self, L.sgl_self]; abel
      · rw [hr'T _ q' (by omega), L.sgl_ne _ (Or.inr hq), L.sgl_ne _ (Or.inr hq)]; simp
  · intro p' q' hp
    rw [map_add, map_smul, K.D_sgl, hc'0, map_zero, smul_zero, add_zero]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [hb' p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, add_zero]

end
end CrystallineSemistableComparison.Auxfm

namespace CrystallineSemistableComparison.Auxfm
section
variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R}

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Conclude with `⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, fun p q h => absurd h (Nat.not_lt_zero _), fun p q h => absurd h (Nat.not_lt_zero _)⟩`. Consider the case `succ k ih`.

Introduce `hk`. Take `⟨a, ha, w, hw, hr, hb⟩` from `ih (by omega)`. Take `⟨q, rfl⟩ : ∃ q, n = k + q` from `⟨n - k, by omega⟩`. Conclude with `surj_step φ s k q (hS k q rfl) (hI k (q + 1) (by omega)) y hy hDy a ha w hw hr hb`.
-/
theorem surj_stage (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ)
    (hS : ∀ p q, p + q = n → SurjUpTo s ((φ.col p).mapH q))
    (hI : ∀ p q, p + q = n + 1 → InjUpTo s ((φ.col p).mapH q))
    (y : ∀ p q, L.X p q) (hy : y ∈ L.T n) (hDy : L.D y = 0) :
    ∀ k, k ≤ n + 1 → ∃ a ∈ K.T n, ∃ w ∈ Bf L n, Sup L k (s ^ (2 * k) • y - Φ φ a - w) ∧ Sup K k (K.D a) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _,
      fun p q h => absurd h (Nat.not_lt_zero _), fun p q h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨a, ha, w, hw, hr, hb⟩ := ih (by omega)
    obtain ⟨q, rfl⟩ : ∃ q, n = k + q := ⟨n - k, by omega⟩
    exact surj_step φ s k q (hS k q rfl) (hI k (q + 1) (by omega)) y hy hDy a ha w hw hr hb

/- English proof (translation)
Take `⟨a, ha, w, hw, hr, hb⟩` from `surj_stage φ s n hS hI y hy hDy (n + 1) le_rfl`. Establish `hrT : s ^ (2 * (n + 1)) • y - Φ φ a - w ∈ L.T n` using `sub_mem (sub_mem (Submodule.smul_mem _ _ hy) (doubleComplexMap_mem_total φ ha)) (Bf_le L hw)`. Establish `hr0 : s ^ (2 * (n + 1)) • y - Φ φ a - w = 0`. Use function extensionality and compare the values at `p q`. Distinguish the cases in `hp : p < n + 1`.

Conclude with `hr p q hp`. Conclude with `hrT p q (by omega)`. Establish `hDaT : K.D a ∈ K.T (n + 1)` using `K.D_mem _ a ha`. Establish `hbc : K.dv (n + 1) 0 (K.D a (n + 1) 0) = 0`. Establish `h` using `congrFun (congrFun (K.DD a) (n + 1)) (0 + 1)`.

Rewrite `h` using `[D_at K hb 0]`. Conclude with `sign_eq_zero h`. Establish `hφb : φ.f (n + 1) 0 (K.D a (n + 1) 0) = 0`. Establish `h` using `congrFun (congrFun (D_res φ y hDy (s ^ (2 * (n + 1))) a hw) (n + 1)) 0`. Rewrite `h` using `[hr0, map_zero, Pi.neg_apply, Pi.neg_apply, Φ_apply]`.

Conclude with `neg_eq_zero.1 h.symm`. Establish `hs` using `inj_get (φ.col (n + 1)) s 0 (hI (n + 1) 0 rfl) _ hbc (by show φ.f (n + 1) 0 (K.D a (n + 1) 0) ∈ _; rw [hφb]; exact Submodule.zero_mem _)`. Establish `hsb : s • K.D a (n + 1) 0 = 0` using `(Submodule.mem_bot R).1 hs`. Use `⟨s • a, Submodule.smul_mem _ _ ha, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`.

Use function extensionality and compare the values at `p q`. Simplify using `only [Pi.smul_apply, Pi.zero_apply]`. Distinguish the cases in `hp : p < n + 1`. Rewrite using `[hb p q hp, smul_zero]`. Distinguish the cases in `h : p = n + 1 ∧ q = 0`.

Take `⟨rfl, rfl⟩` from `h`. Conclude with `hsb`. Rewrite using `[hDaT p q (by omega), smul_zero]`. Establish `e : Φ φ (s • a) - s ^ (2 * n + 3) • y = - (s • w) - s • (s ^ (2 * (n + 1)) • y - Φ φ a - w)`. Rewrite using `[map_smul, show 2 * n + 3 = 2 * (n + 1) + 1 by ring, pow_succ s (2 * (n + 1)), mul_smul, smul_comm (s ^ (2 * (n + 1))) s y, smul_sub, smul_sub]; abel`.

Rewrite using `[e, hr0, smul_zero, sub_zero]`. Conclude with `neg_mem (Submodule.smul_mem _ _ hw)`.
-/
theorem surj_main (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ)
    (hS : ∀ p q, p + q = n → SurjUpTo s ((φ.col p).mapH q))
    (hI : ∀ p q, p + q = n + 1 → InjUpTo s ((φ.col p).mapH q))
    (y : ∀ p q, L.X p q) (hy : y ∈ L.T n) (hDy : L.D y = 0) :
    ∃ x ∈ K.T n, K.D x = 0 ∧ Φ φ x - s ^ (2 * n + 3) • y ∈ Bf L n := by
  obtain ⟨a, ha, w, hw, hr, hb⟩ := surj_stage φ s n hS hI y hy hDy (n + 1) le_rfl
  have hrT : s ^ (2 * (n + 1)) • y - Φ φ a - w ∈ L.T n :=
    sub_mem (sub_mem (Submodule.smul_mem _ _ hy) (doubleComplexMap_mem_total φ ha)) (Bf_le L hw)
  have hr0 : s ^ (2 * (n + 1)) • y - Φ φ a - w = 0 := by
    funext p q
    by_cases hp : p < n + 1
    · exact hr p q hp
    · exact hrT p q (by omega)
  have hDaT : K.D a ∈ K.T (n + 1) := K.D_mem _ a ha
  have hbc : K.dv (n + 1) 0 (K.D a (n + 1) 0) = 0 := by
    have h := congrFun (congrFun (K.DD a) (n + 1)) (0 + 1)
    rw [D_at K hb 0] at h
    exact sign_eq_zero h
  have hφb : φ.f (n + 1) 0 (K.D a (n + 1) 0) = 0 := by
    have h := congrFun (congrFun (D_res φ y hDy (s ^ (2 * (n + 1))) a hw) (n + 1)) 0
    rw [hr0, map_zero, Pi.neg_apply, Pi.neg_apply, Φ_apply] at h
    exact neg_eq_zero.1 h.symm
  have hs := inj_get (φ.col (n + 1)) s 0 (hI (n + 1) 0 rfl) _ hbc
    (by show φ.f (n + 1) 0 (K.D a (n + 1) 0) ∈ _; rw [hφb]; exact Submodule.zero_mem _)
  have hsb : s • K.D a (n + 1) 0 = 0 := (Submodule.mem_bot R).1 hs
  refine ⟨s • a, Submodule.smul_mem _ _ ha, ?_, ?_⟩
  · rw [map_smul]
    funext p q
    simp only [Pi.smul_apply, Pi.zero_apply]
    by_cases hp : p < n + 1
    · rw [hb p q hp, smul_zero]
    · by_cases h : p = n + 1 ∧ q = 0
      · obtain ⟨rfl, rfl⟩ := h; exact hsb
      · rw [hDaT p q (by omega), smul_zero]
  · have e : Φ φ (s • a) - s ^ (2 * n + 3) • y = - (s • w) - s • (s ^ (2 * (n + 1)) • y - Φ φ a - w) := by
      rw [map_smul, show 2 * n + 3 = 2 * (n + 1) + 1 by ring, pow_succ s (2 * (n + 1)), mul_smul,
        smul_comm (s ^ (2 * (n + 1))) s y, smul_sub, smul_sub]; abel
    rw [e, hr0, smul_zero, sub_zero]
    exact neg_mem (Submodule.smul_mem _ _ hw)

end
end CrystallineSemistableComparison.Auxfm

/- English proof (translation)
Introduce `R _ K L φ s n hS hI`. Apply `CrystallineSemistableComparison.Auxfm.surj_mk` to reduce the goal to its premises. Introduce `y hy`. Establish `hDy : L.D y.1 = 0` using `congrArg Subtype.val hy`. Take `⟨x, hx, hDx, hm⟩` from `CrystallineSemistableComparison.Auxfm.surj_main φ s n hS hI y.1 y.2 hDy`.

Use `⟨⟨x, hx⟩, Subtype.ext hDx, ?_⟩` and prove the remaining obligations. Rewrite using `[CrystallineSemistableComparison.Auxfm.tot_B]`. Conclude with `hm`.
-/
theorem CrystallineSemistableComparison.P.dc_map_col_surj : ∀ {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ), (∀ p q, p + q = n → SurjUpTo s ((φ.col p).mapH q)) → (∀ p q, p + q = n + 1 → InjUpTo s ((φ.col p).mapH q)) → SurjUpTo (s ^ (2 * n + 3)) (φ.tot.mapH n) := by
  intro R _ K L φ s n hS hI
  apply CrystallineSemistableComparison.Auxfm.surj_mk
  intro y hy
  have hDy : L.D y.1 = 0 := congrArg Subtype.val hy
  obtain ⟨x, hx, hDx, hm⟩ := CrystallineSemistableComparison.Auxfm.surj_main φ s n hS hI y.1 y.2 hDy
  refine ⟨⟨x, hx⟩, Subtype.ext hDx, ?_⟩
  rw [CrystallineSemistableComparison.Auxfm.tot_B]
  exact hm

namespace CrystallineSemistableComparison.Auxfm
section
variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R}

/- English proof (translation)
Use `show _ ∈ (K.T n).map K.D`. Conclude with `⟨z, hz, rfl⟩`.
-/
theorem D_mem_Bf {n : ℕ} {z : ∀ p q, K.X p q} (hz : z ∈ K.T n) : K.D z ∈ Bf K (n + 1) := by
  show _ ∈ (K.T n).map K.D
  exact ⟨z, hz, rfl⟩

/- English proof (translation)
Establish `hc : K.dv n 0 (e n 0) = 0`. Establish `h` using `congrFun (congrFun hDe n) (0 + 1)`. Rewrite `h` using `[D_at K hS 0]`. Conclude with `sign_eq_zero h`. Establish `hφ : φ.f n 0 (e n 0) = 0` using `congrFun (congrFun hΦ n) 0`.

Establish `hs` using `inj_get (φ.col n) s 0 hI _ hc (by show φ.f n 0 (e n 0) ∈ _; rw [hφ]; exact Submodule.zero_mem _)`. Establish `hsb : s • e n 0 = 0` using `(Submodule.mem_bot R).1 hs`. Use function extensionality and compare the values at `p q`. Simplify using `only [Pi.smul_apply, Pi.zero_apply]`. Distinguish the cases in `hp : p < n`.

Rewrite using `[hS p q hp, smul_zero]`. Distinguish the cases in `h : p = n ∧ q = 0`. Take `⟨rfl, rfl⟩` from `h`. Conclude with `hsb`. Rewrite using `[he p q (by omega), smul_zero]`.
-/
theorem inj_last (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ) (hI : InjUpTo s ((φ.col n).mapH 0))
    (e : ∀ p q, K.X p q) (he : e ∈ K.T n) (hDe : K.D e = 0) (hS : Sup K n e) (hΦ : Φ φ e = 0) : s • e = 0 := by
  have hc : K.dv n 0 (e n 0) = 0 := by
    have h := congrFun (congrFun hDe n) (0 + 1)
    rw [D_at K hS 0] at h
    exact sign_eq_zero h
  have hφ : φ.f n 0 (e n 0) = 0 := congrFun (congrFun hΦ n) 0
  have hs := inj_get (φ.col n) s 0 hI _ hc (by show φ.f n 0 (e n 0) ∈ _; rw [hφ]; exact Submodule.zero_mem _)
  have hsb : s • e n 0 = 0 := (Submodule.mem_bot R).1 hs
  funext p q
  simp only [Pi.smul_apply, Pi.zero_apply]
  by_cases hp : p < n
  · rw [hS p q hp, smul_zero]
  · by_cases h : p = n ∧ q = 0
    · obtain ⟨rfl, rfl⟩ := h; exact hsb
    · rw [he p q (by omega), smul_zero]

/- English proof (translation)
Establish `heT : s ^ (2 * k) • x - g ∈ K.T (k + j + 1)` using `sub_mem (Submodule.smul_mem _ _ hx) (Bf_le K hg)`. Establish `hDe : K.D (s ^ (2 * k) • x - g) = 0` using `by rw [map_sub, map_smul, hDx, D_Bf K hg, smul_zero, sub_zero]`. Use `set e := s ^ (2 * k) • x - g with he_def`. Establish `hec : K.dv k (j + 1) (e k (j + 1)) = 0`. Establish `h` using `congrFun (congrFun hDe k) (j + 1 + 1)`.

Rewrite `h` using `[D_at K he (j + 1)]`. Conclude with `sign_eq_zero h`. Establish `hφe : (φ.col k).f (j + 1) (e k (j + 1)) ∈ (L.col k).B (j + 1)`. Use `⟨(-1 : ℤ) ^ k • t k j, ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hΦ k) (j + 1)`.

Rewrite `h` using `[D_at L htk j, Φ_apply]`. Express the relevant statement in the definitionally equal form `L.dv k j ((-1 : ℤ) ^ k • t k j) = φ.f k (j + 1) (e k (j + 1))`. Rewrite using `[map_zsmul, h]`. Take `⟨c, hc⟩` from `inj_get (φ.col k) s (j + 1) hI _ hec hφe`. Express the relevant statement in the definitionally equal form `K.dv k j c = s • e k (j + 1) at hc`.

Establish `hgm : K.D ((-1 : ℤ) ^ k • K.sgl k j c) ∈ Bf K (k + j + 1)` using `D_mem_Bf (zsmul_mem (sgl_mem K rfl c) _)`. Establish `e1 : s ^ (2 * k + 1) • x - (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) = s • e - K.D ((-1 : ℤ) ^ k • K.sgl k j c)`. Rewrite using `[he_def, pow_succ s (2 * k), mul_smul, smul_comm (s ^ (2 * k)) s x, smul_sub]`. Normalize the expressions using the abelian group laws. Use `set e' := s • e - K.D ((-1 : ℤ) ^ k • K.sgl k j c) with he'_def`.

Establish `he'k : Sup K (k + 1) e'`. Introduce `p' q' hp`. Rewrite using `[he'_def, map_zsmul, K.D_sgl, smul_add, unsign]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]`. Rewrite using `[K.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp` into its components or cases. Rewrite using `[he p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]`. Substitute `hp` using the available equality. Distinguish the cases in `hq : q' = j + 1`. Substitute `hq` using the available equality.

Rewrite using `[K.sgl_self, ← hc, sub_self]`. Rewrite using `[heT _ q' (by omega), K.sgl_ne _ (Or.inr hq), smul_zero, sub_zero]`. Establish `ht'T : s • t - (-1 : ℤ) ^ k • L.sgl k j (φ.f k j c) ∈ L.T (k + j)` using `sub_mem (Submodule.smul_mem _ _ ht) (zsmul_mem (sgl_mem L rfl _) _)`. Use `set t' := s • t - (-1 : ℤ) ^ k • L.sgl k j (φ.f k j c) with ht'_def`. Establish `hΦ' : Φ φ e' = L.D t'`.

Rewrite using `[he'_def, ht'_def]`. Simplify using `only [map_sub, map_smul, map_zsmul, Φ_D, Φ_sgl, hΦ]`. Establish `ht'k : Sup L k t'`. Introduce `p' q' hp`. Rewrite using `[ht'_def]`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply]`. Rewrite using `[htk p' q' hp, L.sgl_ne _ (Or.inl (by omega)), smul_zero, smul_zero, sub_zero]`. Establish `ht'c : L.dv k j (t' k j) = 0`. Establish `h` using `congrFun (congrFun hΦ' k) (j + 1)`. Rewrite `h` using `[D_at L ht'k j, Φ_apply, he'k k (j + 1) (by omega), map_zero]`.

Conclude with `sign_eq_zero h.symm`. Take `⟨c', hc'0, hc'⟩` from `surj_get (φ.col k) s j hS (t' k j) ht'c`. Express the relevant statement in the definitionally equal form `K.dv k j c' = 0 at hc'0`. Express the relevant statement in the definitionally equal form `φ.f k j c' - s • t' k j ∈ _ at hc'`. Take `⟨w₀, hw₀, hw₀e⟩` from `colB _ hc'`.

Establish `e2 : s ^ (2 * (k + 1)) • x - (s • (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) + K.D (K.sgl k j c')) = s • e' - K.D (K.sgl k j c')`. Rewrite using `[← e1, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ s (2 * k + 1), mul_smul, smul_comm (s ^ (2 * k + 1)) s x, smul_sub]; abel`. Use `⟨s • (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) + K.D (K.sgl k j c'), add_mem (Submodule.smul_mem _ _ (add_mem (Submodule.smul_mem _ _ hg) hgm)) (D_mem_Bf (sgl_mem K rfl c')), s • t' - L.sgl k j (φ.f k j c') + w₀, add_mem (sub_mem (Submodule.smul_mem _ _ ht'T) (sgl_mem L rfl _)) …` and prove the remaining obligations. Introduce `p' q' hp`. Rewrite using `[e2, K.D_sgl, hc'0, map_zero, smul_zero, add_zero]`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply]`. Rewrite using `[he'k p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]`. Rewrite using `[e2]`. Simplify using `only [map_sub, map_smul, map_add, Φ_D, Φ_sgl, hΦ', D_Bf L hw₀, add_zero]`. Introduce `p' q' hp`.

Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]`. Rewrite using `[hw₀e p' q' (by omega)]`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp` into its components or cases. Rewrite using `[ht'k p' q' hp, L.sgl_ne _ (Or.inl (by omega)), L.sgl_ne _ (Or.inl (by omega))]; simp`. Substitute `hp` using the available equality.

Distinguish the cases in `hq : q' = j`. Substitute `hq` using the available equality. Rewrite using `[L.sgl_self, L.sgl_self]`. Normalize the expressions using the abelian group laws. Rewrite using `[ht'T _ q' (by omega), L.sgl_ne _ (Or.inr hq), L.sgl_ne _ (Or.inr hq)]; simp`.
-/
theorem inj_step (φ : DCx.Hom K L (RingHom.id R)) (s : R) (k j : ℕ)
    (hS : SurjUpTo s ((φ.col k).mapH j)) (hI : InjUpTo s ((φ.col k).mapH (j + 1)))
    (x : ∀ p q, K.X p q) (hx : x ∈ K.T (k + j + 1)) (hDx : K.D x = 0)
    (g : ∀ p q, K.X p q) (hg : g ∈ Bf K (k + j + 1)) (t : ∀ p q, L.X p q) (ht : t ∈ L.T (k + j))
    (he : Sup K k (s ^ (2 * k) • x - g)) (hΦ : Φ φ (s ^ (2 * k) • x - g) = L.D t) (htk : Sup L k t) :
    ∃ g ∈ Bf K (k + j + 1), ∃ t ∈ L.T (k + j), Sup K (k + 1) (s ^ (2 * (k + 1)) • x - g) ∧
      Φ φ (s ^ (2 * (k + 1)) • x - g) = L.D t ∧ Sup L (k + 1) t := by
  have heT : s ^ (2 * k) • x - g ∈ K.T (k + j + 1) := sub_mem (Submodule.smul_mem _ _ hx) (Bf_le K hg)
  have hDe : K.D (s ^ (2 * k) • x - g) = 0 := by rw [map_sub, map_smul, hDx, D_Bf K hg, smul_zero, sub_zero]
  set e := s ^ (2 * k) • x - g with he_def
  have hec : K.dv k (j + 1) (e k (j + 1)) = 0 := by
    have h := congrFun (congrFun hDe k) (j + 1 + 1)
    rw [D_at K he (j + 1)] at h
    exact sign_eq_zero h
  have hφe : (φ.col k).f (j + 1) (e k (j + 1)) ∈ (L.col k).B (j + 1) := by
    refine ⟨(-1 : ℤ) ^ k • t k j, ?_⟩
    have h := congrFun (congrFun hΦ k) (j + 1)
    rw [D_at L htk j, Φ_apply] at h
    change L.dv k j ((-1 : ℤ) ^ k • t k j) = φ.f k (j + 1) (e k (j + 1))
    rw [map_zsmul, h]
  obtain ⟨c, hc⟩ := inj_get (φ.col k) s (j + 1) hI _ hec hφe
  change K.dv k j c = s • e k (j + 1) at hc
  have hgm : K.D ((-1 : ℤ) ^ k • K.sgl k j c) ∈ Bf K (k + j + 1) := D_mem_Bf (zsmul_mem (sgl_mem K rfl c) _)
  have e1 : s ^ (2 * k + 1) • x - (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) =
      s • e - K.D ((-1 : ℤ) ^ k • K.sgl k j c) := by
    rw [he_def, pow_succ s (2 * k), mul_smul, smul_comm (s ^ (2 * k)) s x, smul_sub]; abel
  set e' := s • e - K.D ((-1 : ℤ) ^ k • K.sgl k j c) with he'_def
  have he'k : Sup K (k + 1) e' := by
    intro p' q' hp
    rw [he'_def, map_zsmul, K.D_sgl, smul_add, unsign]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
    rw [K.sgl_ne _ (Or.inl (by omega)), smul_zero, zero_add]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · rw [he p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
    · subst hp
      by_cases hq : q' = j + 1
      · subst hq; rw [K.sgl_self, ← hc, sub_self]
      · rw [heT _ q' (by omega), K.sgl_ne _ (Or.inr hq), smul_zero, sub_zero]
  have ht'T : s • t - (-1 : ℤ) ^ k • L.sgl k j (φ.f k j c) ∈ L.T (k + j) :=
    sub_mem (Submodule.smul_mem _ _ ht) (zsmul_mem (sgl_mem L rfl _) _)
  set t' := s • t - (-1 : ℤ) ^ k • L.sgl k j (φ.f k j c) with ht'_def
  have hΦ' : Φ φ e' = L.D t' := by
    rw [he'_def, ht'_def]
    simp only [map_sub, map_smul, map_zsmul, Φ_D, Φ_sgl, hΦ]
  have ht'k : Sup L k t' := by
    intro p' q' hp
    rw [ht'_def]; simp only [Pi.sub_apply, Pi.smul_apply]
    rw [htk p' q' hp, L.sgl_ne _ (Or.inl (by omega)), smul_zero, smul_zero, sub_zero]
  have ht'c : L.dv k j (t' k j) = 0 := by
    have h := congrFun (congrFun hΦ' k) (j + 1)
    rw [D_at L ht'k j, Φ_apply, he'k k (j + 1) (by omega), map_zero] at h
    exact sign_eq_zero h.symm
  obtain ⟨c', hc'0, hc'⟩ := surj_get (φ.col k) s j hS (t' k j) ht'c
  change K.dv k j c' = 0 at hc'0
  change φ.f k j c' - s • t' k j ∈ _ at hc'
  obtain ⟨w₀, hw₀, hw₀e⟩ := colB _ hc'
  have e2 : s ^ (2 * (k + 1)) • x - (s • (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) + K.D (K.sgl k j c')) =
      s • e' - K.D (K.sgl k j c') := by
    rw [← e1, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ s (2 * k + 1), mul_smul,
      smul_comm (s ^ (2 * k + 1)) s x, smul_sub]; abel
  refine ⟨s • (s • g + K.D ((-1 : ℤ) ^ k • K.sgl k j c)) + K.D (K.sgl k j c'),
    add_mem (Submodule.smul_mem _ _ (add_mem (Submodule.smul_mem _ _ hg) hgm)) (D_mem_Bf (sgl_mem K rfl c')),
    s • t' - L.sgl k j (φ.f k j c') + w₀,
    add_mem (sub_mem (Submodule.smul_mem _ _ ht'T) (sgl_mem L rfl _)) (Bf_le L hw₀), ?_, ?_, ?_⟩
  · intro p' q' hp
    rw [e2, K.D_sgl, hc'0, map_zero, smul_zero, add_zero]
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [he'k p' q' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
  · rw [e2]
    simp only [map_sub, map_smul, map_add, Φ_D, Φ_sgl, hΦ', D_Bf L hw₀, add_zero]
  · intro p' q' hp
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [hw₀e p' q' (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | hp
    · rw [ht'k p' q' hp, L.sgl_ne _ (Or.inl (by omega)), L.sgl_ne _ (Or.inl (by omega))]; simp
    · subst hp
      by_cases hq : q' = j
      · subst hq; rw [L.sgl_self, L.sgl_self]; abel
      · rw [ht'T _ q' (by omega), L.sgl_ne _ (Or.inr hq), L.sgl_ne _ (Or.inr hq)]; simp

end
end CrystallineSemistableComparison.Auxfm

namespace CrystallineSemistableComparison.Auxfm
section
variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R}

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _; exact ⟨0, Submodule.zero_mem _, z, hz, fun p q h => absurd h (Nat.not_lt_zero _), by simp [hΦx], fun p q h => absurd h (Nat.not_lt_zero _)⟩`. Consider the case `succ k ih`. Introduce `hk`.

Take `⟨g, hg, t, ht, he, hΦ, htk⟩` from `ih (by omega)`. Take `⟨j, rfl⟩ : ∃ j, m = k + j` from `⟨m - k, by omega⟩`. Conclude with `inj_step φ s k j (hS k j (by omega)) (hI k (j + 1) (by omega)) x hx hDx g hg t ht he hΦ htk`.
-/
theorem inj_stage (φ : DCx.Hom K L (RingHom.id R)) (s : R) (m : ℕ)
    (hS : ∀ p q, p + q + 1 = m + 1 → SurjUpTo s ((φ.col p).mapH q))
    (hI : ∀ p q, p + q = m + 1 → InjUpTo s ((φ.col p).mapH q))
    (x : ∀ p q, K.X p q) (hx : x ∈ K.T (m + 1)) (hDx : K.D x = 0)
    (z : ∀ p q, L.X p q) (hz : z ∈ L.T m) (hΦx : Φ φ x = L.D z) :
    ∀ k, k ≤ m + 1 → ∃ g ∈ Bf K (m + 1), ∃ t ∈ L.T m, Sup K k (s ^ (2 * k) • x - g) ∧
      Φ φ (s ^ (2 * k) • x - g) = L.D t ∧ Sup L k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, Submodule.zero_mem _, z, hz, fun p q h => absurd h (Nat.not_lt_zero _),
      by simp [hΦx], fun p q h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, hg, t, ht, he, hΦ, htk⟩ := ih (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
    exact inj_step φ s k j (hS k j (by omega)) (hI k (j + 1) (by omega)) x hx hDx g hg t ht he hΦ htk

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Establish `hΦ : Φ φ x = 0` using `(Submodule.mem_bot R).1 hb`. Establish `h0` using `inj_last φ s 0 (hI 0 0 rfl) x hx hDx (fun p q h => absurd h (Nat.not_lt_zero _)) hΦ`. Rewrite using `[show 2 * 0 + 3 = 2 + 1 by rfl, pow_succ s 2, mul_smul, h0, smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ m`. Take `⟨z, hz, hzx⟩` from `hb`. Take `⟨g, hg, t, ht, he, hΦ, htk⟩` from `inj_stage φ s m hS hI x hx hDx z hz hzx.symm (m + 1) le_rfl`. Establish `ht0 : t = 0`.

Use function extensionality and compare the values at `p q`. Distinguish the cases in `hp : p < m + 1`. Conclude with `htk p q hp`. Conclude with `ht p q (by omega)`. Establish `heT` using `sub_mem (Submodule.smul_mem _ (s ^ (2 * (m + 1))) hx) (Bf_le K hg)`.

Establish `hDe : K.D (s ^ (2 * (m + 1)) • x - g) = 0`. Rewrite using `[map_sub, map_smul, hDx, D_Bf K hg, smul_zero, sub_zero]`. Establish `h0` using `inj_last φ s (m + 1) (hI (m + 1) 0 rfl) _ heT hDe he (by rw [hΦ, ht0, map_zero])`. Rewrite `h0` using `[smul_sub, sub_eq_zero]`. Establish `e : s ^ (2 * (m + 1) + 3) • x = s ^ 2 • (s • g)`.

Rewrite using `[show 2 * (m + 1) + 3 = 2 * (m + 1) + 1 + 2 by ring, pow_add, mul_comm (s ^ (2 * (m + 1) + 1)) (s ^ 2), mul_smul, pow_succ s (2 * (m + 1)), mul_comm (s ^ (2 * (m + 1))) s, mul_smul, h0]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hg)`.
-/
theorem inj_main (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ)
    (hS : ∀ p q, p + q + 1 = n → SurjUpTo s ((φ.col p).mapH q))
    (hI : ∀ p q, p + q = n → InjUpTo s ((φ.col p).mapH q))
    (x : ∀ p q, K.X p q) (hx : x ∈ K.T n) (hDx : K.D x = 0) (hb : Φ φ x ∈ Bf L n) :
    s ^ (2 * n + 3) • x ∈ Bf K n := by
  cases n with
  | zero =>
    have hΦ : Φ φ x = 0 := (Submodule.mem_bot R).1 hb
    have h0 := inj_last φ s 0 (hI 0 0 rfl) x hx hDx (fun p q h => absurd h (Nat.not_lt_zero _)) hΦ
    rw [show 2 * 0 + 3 = 2 + 1 by rfl, pow_succ s 2, mul_smul, h0, smul_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨z, hz, hzx⟩ := hb
    obtain ⟨g, hg, t, ht, he, hΦ, htk⟩ := inj_stage φ s m hS hI x hx hDx z hz hzx.symm (m + 1) le_rfl
    have ht0 : t = 0 := by
      funext p q
      by_cases hp : p < m + 1
      · exact htk p q hp
      · exact ht p q (by omega)
    have heT := sub_mem (Submodule.smul_mem _ (s ^ (2 * (m + 1))) hx) (Bf_le K hg)
    have hDe : K.D (s ^ (2 * (m + 1)) • x - g) = 0 := by
      rw [map_sub, map_smul, hDx, D_Bf K hg, smul_zero, sub_zero]
    have h0 := inj_last φ s (m + 1) (hI (m + 1) 0 rfl) _ heT hDe he (by rw [hΦ, ht0, map_zero])
    rw [smul_sub, sub_eq_zero] at h0
    have e : s ^ (2 * (m + 1) + 3) • x = s ^ 2 • (s • g) := by
      rw [show 2 * (m + 1) + 3 = 2 * (m + 1) + 1 + 2 by ring, pow_add, mul_comm (s ^ (2 * (m + 1) + 1)) (s ^ 2),
        mul_smul, pow_succ s (2 * (m + 1)), mul_comm (s ^ (2 * (m + 1))) s, mul_smul, h0]
    rw [e]; exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hg)

def flipHom (φ : DCx.Hom K L (RingHom.id R)) : DCx.Hom K.flip L.flip (RingHom.id R) :=
  ⟨fun p q => φ.f q p, fun p q x => φ.cv q p x, fun p q x => φ.ch q p x⟩

end
end CrystallineSemistableComparison.Auxfm

/- English proof (translation)
Introduce `R _ K L φ s n hS hI`. Apply `CrystallineSemistableComparison.Auxfm.inj_mk` to reduce the goal to its premises. Introduce `x hx hb`. Rewrite `hb`, the goal using `[CrystallineSemistableComparison.Auxfm.tot_B]`. Conclude with `CrystallineSemistableComparison.Auxfm.inj_main φ s n hS hI x.1 x.2 (congrArg Subtype.val hx) hb`.
-/
theorem CrystallineSemistableComparison.P.dc_map_col_inj : ∀ {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ), (∀ p q, p + q + 1 = n → SurjUpTo s ((φ.col p).mapH q)) → (∀ p q, p + q = n → InjUpTo s ((φ.col p).mapH q)) → InjUpTo (s ^ (2 * n + 3)) (φ.tot.mapH n) := by
  intro R _ K L φ s n hS hI
  apply CrystallineSemistableComparison.Auxfm.inj_mk
  intro x hx hb
  rw [CrystallineSemistableComparison.Auxfm.tot_B] at hb ⊢
  exact CrystallineSemistableComparison.Auxfm.inj_main φ s n hS hI x.1 x.2 (congrArg Subtype.val hx) hb

/- English proof (translation)
Introduce `R _ K L φ s n h`. Conclude with `⟨CrystallineSemistableComparison.P.dc_map_col_inj φ s n (fun p q _ => (h p q (by omega)).2) (fun p q _ => (h p q (by omega)).1), CrystallineSemistableComparison.P.dc_map_col_surj φ s n (fun p q _ => (h p q (by omega)).2) (fun p q _ => (h p q (by omega)).1)⟩`.
-/
theorem CrystallineSemistableComparison.P.dc_map_col : ∀ {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} (φ : DCx.Hom K L (RingHom.id R)) (s : R) (n : ℕ), (∀ p q, p + q ≤ n + 1 → UpTo s ((φ.col p).mapH q)) → UpTo (s ^ (2 * n + 3)) (φ.tot.mapH n) := by
  intro R _ K L φ s n h
  exact ⟨CrystallineSemistableComparison.P.dc_map_col_inj φ s n (fun p q _ => (h p q (by omega)).2) (fun p q _ => (h p q (by omega)).1),
    CrystallineSemistableComparison.P.dc_map_col_surj φ s n (fun p q _ => (h p q (by omega)).2) (fun p q _ => (h p q (by omega)).1)⟩
