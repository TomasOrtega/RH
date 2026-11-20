import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnimodDiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeTate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

def form (D : Datum H) : D.La →+ D.La →+ ℤ :=
  AddMonoidHom.mk' (fun x => (D.EF x).toAddMonoidHom) fun a b => by rw [map_add]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem form_apply (x y : D.La) : form D x y = D.EF x y := rfl

/- English proof (translation)
Use `⟨fun x y => ?_, D.adj, fun x y h => D.unimod.1 (LinearMap.ext fun a => DFunLike.congr_fun h a), fun f => ?_⟩` and prove the remaining obligations. Conclude with `(LinearMap.IsAlt.neg (B := D.EF) D.alt y x).symm`. Take `⟨x, hx⟩` from `D.unimod.2 f.toIntLinearMap`. Conclude with `⟨x, AddMonoidHom.ext fun a => LinearMap.congr_fun hx a⟩`.
-/
theorem form_isUnimod (D : Datum H) : IsUnimod H.bar (form D) := by
  refine ⟨fun x y => ?_, D.adj, fun x y h => D.unimod.1 (LinearMap.ext fun a => DFunLike.congr_fun h a),
    fun f => ?_⟩
  · exact (LinearMap.IsAlt.neg (B := D.EF) D.alt y x).symm
  · obtain ⟨x, hx⟩ := D.unimod.2 f.toIntLinearMap
    exact ⟨x, AddMonoidHom.ext fun a => LinearMap.congr_fun hx a⟩

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

def evHom (I : TateIso D k Q act e) (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl

/- English proof (translation)
The claim follows from `(evHom I n).map_zero`.
-/
theorem ev_zero (I : TateIso D k Q act e) (n : ℕ) : I.ev n 0 = 1 := (evHom I n).map_zero

/- English proof (translation)
The claim follows from `(evHom I n).map_nsmul m a`.
-/
theorem ev_nsmul (I : TateIso D k Q act e) (n m : ℕ) (a : D.La) : I.ev n (m • a) = I.ev n a ^ m :=
  (evHom I n).map_nsmul m a

/- English proof (translation)
The claim follows from `(evHom I n).map_sub a b`.
-/
theorem ev_sub (I : TateIso D k Q act e) (n : ℕ) (a b : D.La) : I.ev n (a - b) = I.ev n a / I.ev n b :=
  (evHom I n).map_sub a b

end

end GlobalTheory.HeckeTate

namespace GlobalTheory

open HeckeTate

/- English proof (translation)
Introduce `h₀ E _ _ _ H D P p k _ Q Q' _ _ act act' e e' I ψ hP hPP hp hpP hψ hact hlow hup hiso hcard huniq he'`. Use `clear h₀`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `hq : 0 < p ^ 2` using `pow_pos hp.pos 2`. Use `D.fin` as an intermediate fact.

Use `D.proj` as an intermediate fact. Use `datum_free_int D` as an intermediate fact. Establish `: Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`. Set `C : Submodule (𝓞 E) D.La` to `{ carrier := {a | ψ (I.ev (p ^ 2) a) = 1} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `ψ _ = 1 at ha hb ⊢`.

Rewrite using `[I.add, map_mul, ha, hb, _root_.one_mul]`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `ψ _ = 1`. Rewrite using `[ev_zero, map_one]`. Use the proof step `smul_mem' := fun c a ha => by`.

Express the relevant statement in the definitionally equal form `ψ _ = 1 at ha ⊢`. Establish `h0` using `hact c (I.ev (p ^ 2) 0)`. Rewrite `h0` using `[← I.lin, smul_zero, ev_zero, map_one]`. Rewrite using `[I.lin, hact, ha, ← h0] }`. Establish `hC : ∀ a, a ∈ C ↔ ψ (I.ev (p ^ 2) a) = 1` using `fun _ => Iff.rfl`.

Establish `hsq : ∀ a, (p ^ 2) • a ∈ C` using `fun a => by`. Rewrite using `[hC, (I.ker _ hq _).2 ⟨a, rfl⟩, map_one]`. Establish `hCiso : ∀ x ∈ C, ∀ y ∈ C, ((p ^ 2 : ℕ) : ℤ) ∣ form D x y` using `fun x hx y hy => by`. Use `huniq _ _ _ _ _ hq ((I.onto _ hq _).2 ⟨x, rfl⟩) ((I.onto _ hq _).2 ⟨y, rfl⟩) (I.isom _ hq x y) (hiso _ _ hx hy)` as an intermediate fact. Conclude with `((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _).1 this`.

Establish `hidx : (nsmulAddMonoidHom (α` using `D.La) (p ^ 2)).range.relIndex C.toAddSubgroup = Nat.card ψ.ker := by`. Set `f : C.toAddSubgroup →+ Additive ψ.ker` to `AddMonoidHom.mk' (fun a => Additive.ofMul ⟨I.ev (p ^ 2) a, a.2⟩) fun a b => by`. Rewrite using `[← ofMul_mul]`. Conclude with `congrArg _ (Subtype.ext (I.add _ _ _))`. Establish `hf : Function.Surjective f` using `fun x => by`.

Take `⟨a, ha⟩` from `(I.onto _ hq _).1 (hup _ x.toMul.2).1`. Conclude with `⟨⟨a, (hC a).2 (ha ▸ x.toMul.2)⟩, Additive.toMul.injective (Subtype.ext ha)⟩`. Establish `hker : f.ker = (nsmulAddMonoidHom (α` using `D.La) (p ^ 2)).range.addSubgroupOf C.toAddSubgroup := by`. Use extensionality with `a`. Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨b, hb⟩` from `(I.ker _ hq a).1 (congrArg (fun z => (z.toMul : Q)) h)`. Conclude with `⟨b, hb.symm⟩`. Introduce and unpack `⟨b, hb⟩`.

Conclude with `Additive.toMul.injective (Subtype.ext ((I.ker _ hq a).2 ⟨b, hb.symm⟩))`. Rewrite using `[AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]`. Both sides reduce to the same expression. Establish `horth` using `mem_of_orth (form D) (form_isUnimod D).bij (m := p ^ 2) (c := Nat.card ψ.ker) hq.ne' (by rw [hcard, datum_finrank_int]; ring) C.toAddSubgroup (by rintro _ ⟨a, rfl⟩; exact hsq a) hidx hCiso`. Take `⟨B', hB', hBB⟩` from `exists_unimod_div (form_isUnimod D) hq.ne' C hsq hCiso horth`.

Establish `hsq' : ∀ a, ∃ y : C, C.subtype y = (p : 𝓞 E) ^ 2 • a` using `fun a => ⟨⟨_, hsq a⟩, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl⟩`. Establish `hlow' : ∀ g ∈ P, ∀ a, ∃ y : C, C.subtype y = (g * p) • a` using `fun g hg a => by`. Take `⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)}` from `Ideal.dvd_iff_le.2 (by simpa using hpP)`. Use `⟨⟨(g * p) • a, hlow J (by rw [hJ, _root_.mul_comm]) (I.ev (p ^ 2) ((g * p) • a)) ?_ fun c hc => ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← ev_nsmul, I.ker _ hq]`.

Use `⟨g • a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨d, hd⟩` from `Ideal.mem_span_singleton.1 (hJ ▸ Ideal.mul_mem_mul hg hc)`. Rewrite using `[← I.lin, I.ker _ hq]`. Use `⟨d • a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]`. Use `congr 1`.

Use `push_cast`. Take the linear combination `(p : 𝓞 E) * hd`. Establish `hrank : Module.finrank (𝓞 E) D.La = Module.finrank (𝓞 E) C`. Use `le_antisymm ?_ C.finrank_le` and prove the remaining obligations. Set `u : D.La →ₗ[𝓞 E] C` to `LinearMap.codRestrict C ((p ^ 2) • LinearMap.id) hsq`.

Use `LinearMap.finrank_le_finrank_of_injective (f := u) fun x y h => ?_` and prove the remaining obligations. Use `(form_isUnimod D).smul_cancel hq.ne' ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Conclude with `congrArg Subtype.val h`. Use `hP.isPrime` as an intermediate fact.

Take `⟨φ, φ', s, hs, hφ, hφ'⟩` from `exists_local_iso hrank P`. Take `⟨G, G1, G2, G3, G4, G5⟩` from `exists_glued (form_isUnimod D) hB' (bar_bar H) hP hPP hp0 hpP C.subtype C.injective_subtype (fun x y => by simpa using hBB x y) hsq' hlow' φ φ' hs hφ hφ'`. Establish `hpos : ∀ n : ℕ, 0 < n → 0 < n * p ^ 2` using `fun n hn => Nat.mul_pos hn hq`. Establish `hdown : ∀ n : ℕ, 0 < n → ∀ a, I.ev (n * p ^ 2) a ^ n = I.ev (p ^ 2) a` using `fun n hn a => by`. Rewrite using `[_root_.mul_comm, I.tower _ _ hq hn]`.

Establish `hkey : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) = 1 ↔ y ∈ mults C (n : 𝓞 E)`. Introduce `n hn y`. Rewrite using `[mem_mults]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨c, hc⟩` from `(I.onto _ hq _).1 (hup _ h).1`. Establish `hcC : c ∈ C` using `(hC c).2 (hc ▸ h)`. Establish `: I.ev (n * p ^ 2) (y - n • c) = 1`. Rewrite using `[ev_sub, ev_nsmul, hdown n hn, hc, div_self']`. Take `⟨b, hb⟩` from `(I.ker _ (hpos n hn) _).1 this`.

Use `⟨⟨c, hcC⟩ + ⟨_, hsq b⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Express the relevant statement in the definitionally equal form `(y : D.La) = n • (c + (p ^ 2) • b)`. Rewrite using `[smul_add, ← mul_smul, ← hb]`. Normalize the expressions using the abelian group laws.

Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Express the relevant statement in the definitionally equal form `ψ (I.ev _ (n • (z : D.La))) = 1`. Rewrite using `[ev_nsmul, hdown n hn]`. Conclude with `z.2`.

Establish `hkey' : ∀ n : ℕ, 0 < n → ∀ y y' : C, y - y' ∈ mults C (n : 𝓞 E) → ψ (I.ev (n * p ^ 2) y) = ψ (I.ev (n * p ^ 2) y')` using `fun n hn y y' h => by`. Use `(hkey n hn _).2 h` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sub, ev_sub, map_div, div_eq_one]`. Then use the resulting hypothesis. Establish `htor : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) ^ n = 1` using `fun n hn y => by`. Rewrite using `[← map_pow, hdown n hn]`.

Conclude with `y.2`. Use `⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n a => ψ (I.ev (n * p ^ 2) (G n a)), fun n a b => ?_, fun n c a => ?_, fun n hn a => ?_, fun n hn x => ⟨fun hx => ?_, ?_⟩, fun n m hn hm a => ?_, fun n hn a b => ?_⟩, rfl, fun n p' hn hpp a => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, Submodule.coe_add, I.add, map_mul]`. Rewrite using `[map_smul, Submodule.coe_smul, I.lin, hact]`. Rewrite using `[hkey n hn]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨b, hb⟩` from `mem_mults.1 (G1 n hn a h)`. Conclude with `⟨b, by rw [hb, Nat.cast_smul_eq_nsmul]⟩`. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `map_mem_mults _ (mem_mults.2 ⟨b, (Nat.cast_smul_eq_nsmul _ _ _).symm⟩)`. Take `⟨x, rfl⟩` from `hψ x`. Establish `h1` using `(hup _ ((map_pow ψ x n).trans hx)).1`. Rewrite `h1` using `[← pow_mul]`. Take `⟨b, rfl⟩` from `(I.onto _ (hpos n hn) _).1 h1`.

Establish `hb : b ∈ C` using `by rw [hC, ← hdown n hn, map_pow, hx]`. Take `⟨a, ha⟩` from `G2 n hn ⟨b, hb⟩`. Conclude with `⟨a, hkey' n hn _ _ ha⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `htor n hn _`.

Rewrite using `[← map_pow, mul_right_comm, I.tower _ _ (hpos n hn) hm]`. Conclude with `hkey' n hn _ _ (G3 n m hn hm a)`. Use `he' n _ _ _ hn (htor n hn _) (htor n hn _) ?_` and prove the remaining obligations. Establish `h1` using `I.isom _ (hpos n hn) (G n a) (G n b)`. Take `⟨t, ht⟩` from `G4 n hn a b`.

Establish `h2 : D.EF (G n a) (G n b) = (p ^ 2 : ℕ) * (D.EF a b + n * t)`. Rewrite using `[← ht, ← form_apply, hBB, form_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2, zpow_mul, zpow_natCast, I.ζ_pow _ _ hn hq, zpow_add, zpow_mul, zpow_natCast, (I.ζ_prim n hn).pow_eq_one, one_zpow, _root_.mul_one]`. Conclude with `h1`.

Establish `hcop : n.Coprime p` using `(Nat.coprime_of_mul_modEq_one p' hpp).symm`. Express the relevant statement in the definitionally equal form `ψ (I.ev (n * p ^ 2) (G n a)) = _`. Rewrite using `[← I.tower n _ hn hq, ← ev_nsmul]`. Use `hkey' n hn _ ⟨_, hsq _⟩ ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `mem_mults.1 (G5 n hn hcop a)`.

Take `⟨t, ht⟩` from `(Nat.modEq_iff_dvd.1 hpp)`. Establish `ht'` using `congrArg (Int.castRingHom (𝓞 E)) ht`. Simplify using `only [eq_intCast] at ht'`. Move the coercions through the operations in `at ht'`. Take `⟨u, v, huv⟩` from `(Nat.isCoprime_iff_coprime.2 (hcop.pow_right 2)).map (Int.castRingHom (𝓞 E))`.

Simplify using `only [eq_intCast, Int.cast_natCast] at huv`. Use `set y : C := G n a - ⟨_, hsq (p' • a)⟩ with hy`. Establish `h1 : (y : D.La) = (n : 𝓞 E) • (b + ((p : 𝓞 E) * t) • a)`. Rewrite using `[smul_add, ← hb, hy, Submodule.coe_sub, Submodule.subtype_apply]`. Simplify using `only [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]`.

Rewrite using `[sub_add, ← sub_smul]`. Use `congr 2`. Use `push_cast`. Take the linear combination `(-(p : 𝓞 E)) * ht'`. Generalize the expression as in `b + ((p : 𝓞 E) * t) • a = z at h1`.

Use `mem_mults.2 ⟨u • y + v • ⟨_, hsq z⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_smul, Submodule.coe_add, h1, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]`. Rewrite using `[← add_smul, huv, one_smul]`.
-/
theorem exists_tateIso_heckeQuotient :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)) := by
  intro h₀ E _ _ _ H D P p k _ Q Q' _ _ act act' e e' I ψ hP hPP hp hpP hψ hact hlow hup hiso hcard huniq he'
  clear h₀
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq : 0 < p ^ 2 := pow_pos hp.pos 2
  have := D.fin
  have := D.proj
  have := datum_free_int D
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let C : Submodule (𝓞 E) D.La :=
    { carrier := {a | ψ (I.ev (p ^ 2) a) = 1}
      add_mem' := fun {a b} ha hb => by
        change ψ _ = 1 at ha hb ⊢
        rw [I.add, map_mul, ha, hb, _root_.one_mul]
      zero_mem' := by
        change ψ _ = 1
        rw [ev_zero, map_one]
      smul_mem' := fun c a ha => by
        change ψ _ = 1 at ha ⊢
        have h0 := hact c (I.ev (p ^ 2) 0)
        rw [← I.lin, smul_zero, ev_zero, map_one] at h0
        rw [I.lin, hact, ha, ← h0] }
  have hC : ∀ a, a ∈ C ↔ ψ (I.ev (p ^ 2) a) = 1 := fun _ => Iff.rfl
  have hsq : ∀ a, (p ^ 2) • a ∈ C := fun a => by
    rw [hC, (I.ker _ hq _).2 ⟨a, rfl⟩, map_one]
  have hCiso : ∀ x ∈ C, ∀ y ∈ C, ((p ^ 2 : ℕ) : ℤ) ∣ form D x y := fun x hx y hy => by
    have := huniq _ _ _ _ _ hq ((I.onto _ hq _).2 ⟨x, rfl⟩) ((I.onto _ hq _).2 ⟨y, rfl⟩)
      (I.isom _ hq x y) (hiso _ _ hx hy)
    exact ((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _).1 this
  have hidx : (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.relIndex C.toAddSubgroup = Nat.card ψ.ker := by
    let f : C.toAddSubgroup →+ Additive ψ.ker := AddMonoidHom.mk'
      (fun a => Additive.ofMul ⟨I.ev (p ^ 2) a, a.2⟩) fun a b => by
        rw [← ofMul_mul]
        exact congrArg _ (Subtype.ext (I.add _ _ _))
    have hf : Function.Surjective f := fun x => by
      obtain ⟨a, ha⟩ := (I.onto _ hq _).1 (hup _ x.toMul.2).1
      exact ⟨⟨a, (hC a).2 (ha ▸ x.toMul.2)⟩, Additive.toMul.injective (Subtype.ext ha)⟩
    have hker : f.ker = (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.addSubgroupOf C.toAddSubgroup := by
      ext a
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      constructor
      · intro h
        obtain ⟨b, hb⟩ := (I.ker _ hq a).1 (congrArg (fun z => (z.toMul : Q)) h)
        exact ⟨b, hb.symm⟩
      · rintro ⟨b, hb⟩
        exact Additive.toMul.injective (Subtype.ext ((I.ker _ hq a).2 ⟨b, hb.symm⟩))
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
      AddSubgroup.card_top]
    rfl
  have horth := mem_of_orth (form D) (form_isUnimod D).bij (m := p ^ 2) (c := Nat.card ψ.ker) hq.ne'
    (by rw [hcard, datum_finrank_int]; ring) C.toAddSubgroup (by rintro _ ⟨a, rfl⟩; exact hsq a) hidx hCiso
  obtain ⟨B', hB', hBB⟩ := exists_unimod_div (form_isUnimod D) hq.ne' C hsq hCiso horth
  have hsq' : ∀ a, ∃ y : C, C.subtype y = (p : 𝓞 E) ^ 2 • a := fun a =>
    ⟨⟨_, hsq a⟩, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl⟩
  have hlow' : ∀ g ∈ P, ∀ a, ∃ y : C, C.subtype y = (g * p) • a := fun g hg a => by
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_iff_le.2 (by simpa using hpP)
    refine ⟨⟨(g * p) • a, hlow J (by rw [hJ, _root_.mul_comm]) (I.ev (p ^ 2) ((g * p) • a)) ?_ fun c hc => ?_⟩, rfl⟩
    · rw [← ev_nsmul, I.ker _ hq]
      refine ⟨g • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hJ ▸ Ideal.mul_mem_mul hg hc)
      rw [← I.lin, I.ker _ hq]
      refine ⟨d • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      linear_combination (p : 𝓞 E) * hd
  have hrank : Module.finrank (𝓞 E) D.La = Module.finrank (𝓞 E) C := by
    refine le_antisymm ?_ C.finrank_le
    let u : D.La →ₗ[𝓞 E] C := LinearMap.codRestrict C ((p ^ 2) • LinearMap.id) hsq
    refine LinearMap.finrank_le_finrank_of_injective (f := u) fun x y h => ?_
    refine (form_isUnimod D).smul_cancel hq.ne' ?_
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact congrArg Subtype.val h
  have := hP.isPrime
  obtain ⟨φ, φ', s, hs, hφ, hφ'⟩ := exists_local_iso hrank P
  obtain ⟨G, G1, G2, G3, G4, G5⟩ := exists_glued (form_isUnimod D) hB' (bar_bar H) hP hPP hp0 hpP C.subtype
    C.injective_subtype (fun x y => by simpa using hBB x y) hsq' hlow' φ φ' hs hφ hφ'
  have hpos : ∀ n : ℕ, 0 < n → 0 < n * p ^ 2 := fun n hn => Nat.mul_pos hn hq
  have hdown : ∀ n : ℕ, 0 < n → ∀ a, I.ev (n * p ^ 2) a ^ n = I.ev (p ^ 2) a := fun n hn a => by
    rw [_root_.mul_comm, I.tower _ _ hq hn]
  have hkey : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) = 1 ↔ y ∈ mults C (n : 𝓞 E) := by
    intro n hn y
    rw [mem_mults]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (I.onto _ hq _).1 (hup _ h).1
      have hcC : c ∈ C := (hC c).2 (hc ▸ h)
      have : I.ev (n * p ^ 2) (y - n • c) = 1 := by
        rw [ev_sub, ev_nsmul, hdown n hn, hc, div_self']
      obtain ⟨b, hb⟩ := (I.ker _ (hpos n hn) _).1 this
      refine ⟨⟨c, hcC⟩ + ⟨_, hsq b⟩, Subtype.ext ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      change (y : D.La) = n • (c + (p ^ 2) • b)
      rw [smul_add, ← mul_smul, ← hb]
      abel
    · rintro ⟨z, rfl⟩
      rw [Nat.cast_smul_eq_nsmul]
      change ψ (I.ev _ (n • (z : D.La))) = 1
      rw [ev_nsmul, hdown n hn]
      exact z.2
  have hkey' : ∀ n : ℕ, 0 < n → ∀ y y' : C, y - y' ∈ mults C (n : 𝓞 E) →
      ψ (I.ev (n * p ^ 2) y) = ψ (I.ev (n * p ^ 2) y') := fun n hn y y' h => by
    have := (hkey n hn _).2 h
    rwa [Submodule.coe_sub, ev_sub, map_div, div_eq_one] at this
  have htor : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) ^ n = 1 := fun n hn y => by
    rw [← map_pow, hdown n hn]
    exact y.2
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n a => ψ (I.ev (n * p ^ 2) (G n a)), fun n a b => ?_, fun n c a => ?_,
    fun n hn a => ?_, fun n hn x => ⟨fun hx => ?_, ?_⟩, fun n m hn hm a => ?_, fun n hn a b => ?_⟩, rfl,
    fun n p' hn hpp a => ?_⟩
  · rw [map_add, Submodule.coe_add, I.add, map_mul]
  · rw [map_smul, Submodule.coe_smul, I.lin, hact]
  · rw [hkey n hn]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := mem_mults.1 (G1 n hn a h)
      exact ⟨b, by rw [hb, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨b, rfl⟩
      exact map_mem_mults _ (mem_mults.2 ⟨b, (Nat.cast_smul_eq_nsmul _ _ _).symm⟩)
  · obtain ⟨x, rfl⟩ := hψ x
    have h1 := (hup _ ((map_pow ψ x n).trans hx)).1
    rw [← pow_mul] at h1
    obtain ⟨b, rfl⟩ := (I.onto _ (hpos n hn) _).1 h1
    have hb : b ∈ C := by rw [hC, ← hdown n hn, map_pow, hx]
    obtain ⟨a, ha⟩ := G2 n hn ⟨b, hb⟩
    exact ⟨a, hkey' n hn _ _ ha⟩
  · rintro ⟨a, rfl⟩
    exact htor n hn _
  · rw [← map_pow, mul_right_comm, I.tower _ _ (hpos n hn) hm]
    exact hkey' n hn _ _ (G3 n m hn hm a)
  · refine he' n _ _ _ hn (htor n hn _) (htor n hn _) ?_
    have h1 := I.isom _ (hpos n hn) (G n a) (G n b)
    obtain ⟨t, ht⟩ := G4 n hn a b
    have h2 : D.EF (G n a) (G n b) = (p ^ 2 : ℕ) * (D.EF a b + n * t) := by
      rw [← ht, ← form_apply, hBB, form_apply]
      ring
    rw [h2, zpow_mul, zpow_natCast, I.ζ_pow _ _ hn hq, zpow_add, zpow_mul, zpow_natCast,
      (I.ζ_prim n hn).pow_eq_one, one_zpow, _root_.mul_one] at h1
    exact h1
  · have hcop : n.Coprime p := (Nat.coprime_of_mul_modEq_one p' hpp).symm
    change ψ (I.ev (n * p ^ 2) (G n a)) = _
    rw [← I.tower n _ hn hq, ← ev_nsmul]
    refine hkey' n hn _ ⟨_, hsq _⟩ ?_
    obtain ⟨b, hb⟩ := mem_mults.1 (G5 n hn hcop a)
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 hpp)
    have ht' := congrArg (Int.castRingHom (𝓞 E)) ht
    simp only [eq_intCast] at ht'
    push_cast at ht'
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 (hcop.pow_right 2)).map (Int.castRingHom (𝓞 E))
    simp only [eq_intCast, Int.cast_natCast] at huv
    set y : C := G n a - ⟨_, hsq (p' • a)⟩ with hy
    have h1 : (y : D.La) = (n : 𝓞 E) • (b + ((p : 𝓞 E) * t) • a) := by
      rw [smul_add, ← hb, hy, Submodule.coe_sub, Submodule.subtype_apply]
      simp only [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
      rw [sub_add, ← sub_smul]
      congr 2
      push_cast
      linear_combination (-(p : 𝓞 E)) * ht'
    generalize b + ((p : 𝓞 E) * t) • a = z at h1
    refine mem_mults.2 ⟨u • y + v • ⟨_, hsq z⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_smul, Submodule.coe_add, h1, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
    rw [← add_smul, huv, one_smul]

end GlobalTheory
