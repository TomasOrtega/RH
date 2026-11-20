import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure Steps : Prop where
  offEx : OffEx
  pairs : Pairs
  pn : PnFacts
  hyp : HypEmb
  cov : FinCov
  fib : FinFib
  comps : Comps
  ring : RingL
  lowT : LowTL
  ptVan : PtVanT
  low : LowL
  tower : TowerL
  aff : AffVan
  twBij : TwBij
  gysT : GysTL
  gys0 : GysinCondition
  qEasy : QEasy
  lim : LimOnto
  qOnto : QOnto
  qProj : QProj
  kunBij : KunBij
  kun : KunL
  swap : Swap
  slice : Slice
  ptInt : PtInt
  detect : DetectL
  dual : DualL
  supp : FinSupp
  cls : PnCls
  inj : InjL
  trComp : TrComp
  div : DivL
  basis : BasisOne
  top : TopPart

namespace Steps
variable (H : Steps) (hI : In) (hT : TrIn) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0)
include H hI hl

/- English proof (translation)
The claim follows from `H.low hI H.ptVan l k hl (H.ring hI l) (H.lowT hI l k hl)`.
-/
theorem low' : Low l k := H.low hI H.ptVan l k hl (H.ring hI l) (H.lowT hI l k hl)

/- English proof (translation)
Take `⟨G⟩` from `H.gys0 hI H.twBij l k hl (H.tower hI l k hl) (H.gysT hI H.offEx k)`. Take `⟨h1, h2, h3⟩` from `H.qEasy l k G`. Conclude with `⟨⟨fun h _ _ hn => G.q h hn, h1, H.qOnto hI H.lim l k hl G, h2, h3, H.qProj hI l k G⟩⟩`.
-/
theorem gysQ : Nonempty (GysQ k l) := by
  obtain ⟨G⟩ := H.gys0 hI H.twBij l k hl (H.tower hI l k hl) (H.gysT hI H.offEx k)
  obtain ⟨h1, h2, h3⟩ := H.qEasy l k G
  exact ⟨⟨fun h _ _ hn => G.q h hn, h1, H.qOnto hI H.lim l k hl G, h2, h3, H.qProj hI l k G⟩⟩

/- English proof (translation)
The claim follows from `H.kun l k d p (H.kunBij hI l k hl (H.ring hI l) d p hp)`.
-/
theorem kun' (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) : Kun l k d p :=
  H.kun l k d p (H.kunBij hI l k hl (H.ring hI l) d p hp)

/- English proof (translation)
Rewrite using `[H.ptInt l k hl d p hp (H.ring hI l) (H.low' hI l k hl) (H.kun' hI l k hl d p hp) lam Λ hΛ y, H.slice H.pairs l k hl d p hp (H.ring hI l) G y]`.
-/
theorem int_pt (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0) (hΛ : IsInt l p lam (add_zero _) Λ) (y : Pt p) :
    pb l y.1 0 (Λ (G.diag d p)) = lam (G.pt d y) • oneV l (S k) := by
  rw [H.ptInt l k hl d p hp (H.ring hI l) (H.low' hI l k hl) (H.kun' hI l k hl d p hp) lam Λ hΛ y,
    H.slice H.pairs l k hl d p hp (H.ring hI l) G y]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `(H.low' hI l k hl).pts p hp.1 _ fun y => ?_` and prove the remaining obligations. Rewrite using `[map_sub, H.int_pt hI l k hl G d p hp lam Λ hΛ y, h1, one_smul, (H.ring hI l).one_nat y.1 (LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)), sub_self]`.
-/
theorem int_one (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0)
    (hΛ : IsInt l p lam (add_zero _) Λ) : Λ (G.diag d p) = oneV l X := by
  rw [← sub_eq_zero]
  refine (H.low' hI l k hl).pts p hp.1 _ fun y => ?_
  rw [map_sub, H.int_pt hI l k hl G d p hp lam Λ hΛ y, h1, one_smul,
    (H.ring hI l).one_nat y.1 (LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)), sub_self]

include hT

/- English proof (translation)
Establish `hR` using `H.ring hI l`. Establish `hL` using `H.low' hI l k hl`. Use `hp.1` as an intermediate fact. Take `⟨t, U, z, hU, hz, hzU⟩` from `H.cls hI H.pn H.hyp H.offEx l k hl hR hL (fun j d n hn => by`. Establish `: NeZero (l ^ j)` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Conclude with `H.aff hI H.ptVan k (l ^ j) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) d n 0 hn) ⟨G⟩ d`. Take `⟨π, hπ, hf, hs⟩` from `H.cov k d p hp hP hX`. Take `⟨s, hs'⟩` from `H.fib k p _ π hπ hf t U hU`. Establish `hinj` using `H.inj hT l π hf hs (H.pn k d).2.1 (H.pn k d).2.2.1 (LPdCut.unit_of (PNto k d) (isUnit_iff_ne_zero.2 hl)) (2 * d)`. Establish `h0 : pb l (π ⁻¹ᵁ U).ι _ (pb l π (2 * d) z) = 0`.

Rewrite using `[← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply, hzU, map_zero]`. Establish `hm` using `H.supp H.offEx H.pairs l k hl hR hL G d p inferInstance hp.2 s _ hs' _ h0`. Assume the negation of the conclusion as `hc`. Establish `hc' : ∀ y : Pt p, G.pt d y = 0` using `fun y => by_contra fun h => hc ⟨y, h⟩`. Rewrite `hm` using `[Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc' y), Submodule.mem_bot]`.

Conclude with `hz (hinj (hm.trans (map_zero _).symm))`.
-/
theorem pt_ne (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ y : Pt p, G.pt d y ≠ 0 := by
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have := hp.1
  obtain ⟨t, U, z, hU, hz, hzU⟩ := H.cls hI H.pn H.hyp H.offEx l k hl hR hL (fun j d n hn => by
    have : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact H.aff hI H.ptVan k (l ^ j) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) d n 0 hn) ⟨G⟩ d
  obtain ⟨π, hπ, hf, hs⟩ := H.cov k d p hp hP hX
  obtain ⟨s, hs'⟩ := H.fib k p _ π hπ hf t U hU
  have hinj := H.inj hT l π hf hs (H.pn k d).2.1 (H.pn k d).2.2.1
    (LPdCut.unit_of (PNto k d) (isUnit_iff_ne_zero.2 hl)) (2 * d)
  have h0 : pb l (π ⁻¹ᵁ U).ι _ (pb l π (2 * d) z) = 0 := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply, hzU, map_zero]
  have hm := H.supp H.offEx H.pairs l k hl hR hL G d p inferInstance hp.2 s _ hs' _ h0
  by_contra hc
  have hc' : ∀ y : Pt p, G.pt d y = 0 := fun y => by_contra fun h => hc ⟨y, h⟩
  rw [Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc' y), Submodule.mem_bot] at hm
  exact hz (hinj (hm.trans (map_zero _).symm))

/- English proof (translation)
Establish `hL` using `H.low' hI l k hl`. Take `⟨y, hy⟩` from `H.pt_ne hI hT l k hl G d p hp hP hX`. Choose the witnesses or unpack the hypotheses as in `⟨lam, hlam⟩ : ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam (G.pt d y) = 1 := by`. Take `⟨f, hf⟩` from `not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ_[l] _).1 hy)`. Conclude with `⟨(f (G.pt d y))⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩`.

Use `⟨lam, fun h => by simp [h] at hlam, fun y' => ?_⟩` and prove the remaining obligations. Take `⟨Λ, hΛ⟩` from `(H.kun' hI l k hl d p hp).int lam 0 (2 * d) (add_zero _)`. Establish `h` using `hL.conn p hp.1 inferInstance (Λ (G.diag d p)) y y'`. Rewrite `h` using `[H.int_pt hI l k hl G d p hp lam Λ hΛ, H.int_pt hI l k hl G d p hp lam Λ hΛ, hlam]`. Conclude with `((hL.line _).unique h rfl)`.
-/
theorem tr_int (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam ≠ 0 ∧ ∀ y : Pt p, lam (G.pt d y) = 1 := by
  have hL := H.low' hI l k hl
  obtain ⟨y, hy⟩ := H.pt_ne hI hT l k hl G d p hp hP hX
  obtain ⟨lam, hlam⟩ : ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam (G.pt d y) = 1 := by
    obtain ⟨f, hf⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ_[l] _).1 hy)
    exact ⟨(f (G.pt d y))⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  refine ⟨lam, fun h => by simp [h] at hlam, fun y' => ?_⟩
  obtain ⟨Λ, hΛ⟩ := (H.kun' hI l k hl d p hp).int lam 0 (2 * d) (add_zero _)
  have h := hL.conn p hp.1 inferInstance (Λ (G.diag d p)) y y'
  rw [H.int_pt hI l k hl G d p hp lam Λ hΛ, H.int_pt hI l k hl G d p hp lam Λ hΛ, hlam] at h
  exact ((hL.line _).unique h rfl)

/- English proof (translation)
The claim follows from `H.detect l k hl d p hp (H.ring hI l) (H.kun' hI l k hl d p hp) lam (G.diag d p) (H.swap H.pairs l k hl d p hp (H.ring hI l) G) (H.int_one hI l k hl G d p hp lam h1)`.
-/
theorem detect' (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) : Detect l d X lam :=
  H.detect l k hl d p hp (H.ring hI l) (H.kun' hI l k hl d p hp) lam (G.diag d p)
    (H.swap H.pairs l k hl d p hp (H.ring hI l) G) (H.int_one hI l k hl G d p hp lam h1)

omit hl [IsAlgClosed k] in
/- English proof (translation)
Introduce `l _ k _ _ hl d X p hp hP hX`. Take `⟨G⟩` from `H.gysQ hI l k hl`. Take `⟨lam, h0, h1⟩` from `H.tr_int hI hT l k hl G d p hp hP hX`. Conclude with `H.dual l k hl d p hp hX (H.ring hI l) (H.low' hI l k hl) lam (H.detect' hI hT l k hl G d p hp lam h1) h0`.
-/
theorem qDual : QDual := by
  intro l _ k _ _ hl d X p hp hP hX
  obtain ⟨G⟩ := H.gysQ hI l k hl
  obtain ⟨lam, h0, h1⟩ := H.tr_int hI hT l k hl G d p hp hP hX
  exact H.dual l k hl d p hp hX (H.ring hI l) (H.low' hI l k hl) lam (H.detect' hI hT l k hl G d p hp lam h1) h0

end Steps

/- English proof (translation)
Take `⟨s, c, a, h⟩` from `h`. Use `FiniteDimensional.of_injective (LinearMap.pi fun t : Fin s => if hn : n + c t = 2 * d then lam ∘ₗ (cupV l X hn).flip (a t) else 0) ((injective_iff_map_eq_zero _).2 fun x hx => ?_)` and prove the remaining obligations. Use `h n x fun t hn => ?_` and prove the remaining obligations. Use `congrFun hx t` as an intermediate fact. Simplify `this` using `[dif_pos hn]`.
-/
theorem Detect.finite {l : ℕ} [Fact l.Prime] {d : ℕ} {X : Scheme.{0}} {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]}
    (h : Detect l d X lam) (n : ℤ) : FiniteDimensional ℚ_[l] (V l X n) := by
  classical
  obtain ⟨s, c, a, h⟩ := h
  refine FiniteDimensional.of_injective (LinearMap.pi fun t : Fin s =>
    if hn : n + c t = 2 * d then lam ∘ₗ (cupV l X hn).flip (a t) else 0) ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
  refine h n x fun t hn => ?_
  have := congrFun hx t
  simpa [dif_pos hn] using this

/- English proof (translation)
Introduce `l _ k _ _ hl d X p hp hP W E π i r c hpb hi hr U hU e he hPB`. Take `⟨G⟩` from `H.gysQ hI l k hl`. Establish `hR` using `H.ring hI l`. Establish `hL` using `H.low' hI l k hl`. Establish `hK` using `H.kun' hI l k hl _ p hp`.

Use `hp.1` as an intermediate fact. Take `⟨lam, h1⟩` from `H.trComp H.comps H.offEx H.pairs l k hl hR G (d + 1) (fun p hp hP hX => by`. Take `⟨lam, -, h⟩` from `H.tr_int hI hT l k hl G _ p hp hP hX`. Conclude with `⟨lam, h⟩) p hp hP`. Establish `hD` using `H.detect' hI hT l k hl G _ p hp lam h1`.

Use `hD.finite (2 * ((d + 1 : ℕ) : ℤ))` as an intermediate fact. Take `⟨s, a, ha⟩` from `H.basis ℚ_[l] _ lam fun h0 => by`. Take `⟨s, c, a, h⟩` from `hD`. Conclude with `subsingleton_of_forall_eq 0 fun x => h _ x fun t hn => by rw [h0]; rfl`. Take `⟨Λ, hΛ⟩` from `hK.int lam 0 _ (add_zero _)`.

Take `⟨b, hb, hδ⟩` from `H.top l k hl _ p hp hR hL hK lam s a ha Λ hΛ (G.diag (d + 1) p)`. Rewrite `hb` using `[H.int_one hI l k hl G _ p hp lam h1 Λ hΛ]`. Establish `hr' : i ≫ π ≫ pullback.fst p p = r` using `by rw [← Category.assoc, hpb.w, Category.assoc, pullback.diagonal_fst, Category.comp_id]`. Establish `hΔ` using `(H.pairs k (d + 1) p inferInstance hp.2).1`. Take `⟨U₀, hU₀⟩` from `H.offEx.1 _ hΔ.cl`.

Establish `hUU : U = π ⁻¹ᵁ U₀` using `TopologicalSpace.Opens.ext (hU.trans (H.offEx.2 _ _ _ _ hpb U₀ hU₀).symm)`. Establish `h0 : pb l U.ι _ (pb l π _ (G.diag (d + 1) p)) = 0`. Rewrite using `[hUU, ← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply]`. Unfold `GysQ.diag GysQ.cls`. Rewrite using `[dif_pos hΔ, G.off hΔ _ U₀ hU₀, map_zero]`.

Establish `hw : (2 : ℤ) + 2 * d = 2 * ((d + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Take `⟨m, hm⟩` from `H.div l k hl hR G p i (π ≫ pullback.fst p p) c (by rwa [Category.assoc]) (by rw [← Category.assoc, hr']; infer_instance) U hU e he (by rwa [hr']) (2 * d) _ hw _ h0`. Establish `key : ∀ (w : ℤ) (hw : 2 + 2 * d = w) (δ : V l (pullback p p) w) (a : Fin s → V l X w), pb l π _ δ = cupV l W hw e m → LinearIndependent ℚ_[l] a → δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w | ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X …`. Introduce and unpack `_ rfl δ a h1 h2 h3`. Conclude with `⟨δ, m, s, a, b, h1, h2, hb, h3⟩`.

Conclude with `key _ hw _ a hm a.linearIndependent hδ`.
-/
theorem Steps.qDiag (H : Steps) (hI : In) (hT : TrIn) : QDiag := by
  intro l _ k _ _ hl d X p hp hP W E π i r c hpb hi hr U hU e he hPB
  obtain ⟨G⟩ := H.gysQ hI l k hl
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have hK := H.kun' hI l k hl _ p hp
  have := hp.1
  obtain ⟨lam, h1⟩ := H.trComp H.comps H.offEx H.pairs l k hl hR G (d + 1) (fun p hp hP hX => by
    obtain ⟨lam, -, h⟩ := H.tr_int hI hT l k hl G _ p hp hP hX
    exact ⟨lam, h⟩) p hp hP
  have hD := H.detect' hI hT l k hl G _ p hp lam h1
  have := hD.finite (2 * ((d + 1 : ℕ) : ℤ))
  obtain ⟨s, a, ha⟩ := H.basis ℚ_[l] _ lam fun h0 => by
    obtain ⟨s, c, a, h⟩ := hD
    exact subsingleton_of_forall_eq 0 fun x => h _ x fun t hn => by rw [h0]; rfl
  obtain ⟨Λ, hΛ⟩ := hK.int lam 0 _ (add_zero _)
  obtain ⟨b, hb, hδ⟩ := H.top l k hl _ p hp hR hL hK lam s a ha Λ hΛ (G.diag (d + 1) p)
  rw [H.int_one hI l k hl G _ p hp lam h1 Λ hΛ] at hb
  have hr' : i ≫ π ≫ pullback.fst p p = r := by rw [← Category.assoc, hpb.w, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hΔ := (H.pairs k (d + 1) p inferInstance hp.2).1
  obtain ⟨U₀, hU₀⟩ := H.offEx.1 _ hΔ.cl
  have hUU : U = π ⁻¹ᵁ U₀ := TopologicalSpace.Opens.ext (hU.trans (H.offEx.2 _ _ _ _ hpb U₀ hU₀).symm)
  have h0 : pb l U.ι _ (pb l π _ (G.diag (d + 1) p)) = 0 := by
    rw [hUU, ← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply]
    unfold GysQ.diag GysQ.cls
    rw [dif_pos hΔ, G.off hΔ _ U₀ hU₀, map_zero]
  have hw : (2 : ℤ) + 2 * d = 2 * ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨m, hm⟩ := H.div l k hl hR G p i (π ≫ pullback.fst p p) c (by rwa [Category.assoc])
    (by rw [← Category.assoc, hr']; infer_instance) U hU e he (by rwa [hr']) (2 * d) _ hw _ h0
  have key : ∀ (w : ℤ) (hw : 2 + 2 * d = w) (δ : V l (pullback p p) w) (a : Fin s → V l X w),
      pb l π _ δ = cupV l W hw e m → LinearIndependent ℚ_[l] a →
      δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
        ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v} →
      ∃ (δ : V l (pullback p p) (2 + 2 * d)) (m : V l W (2 * d)) (s : ℕ) (a : Fin s → V l X (2 + 2 * d)) (b : Fin s → V l X 0),
        pb l π _ δ = cupV l W rfl e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ t, b t = oneV l X ∧
        δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 + 2 * d) |
          ∃ (n n' : ℤ) (h : n + n' = 2 + 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v} := by
    rintro _ rfl δ a h1 h2 h3
    exact ⟨δ, m, s, a, b, h1, h2, hb, h3⟩
  exact key _ hw _ a hm a.linearIndependent hδ

end UpperTheory.Gal.KunnethLefschetz
