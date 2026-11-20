import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinV
import Development.WeilBound.ThetaLifts.LatticeBasics.SecondFromFirstStatement
import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
  {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM F Y.J)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (κ ⊕ κ)}
  {om : G2 σ Y →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)} {K : Subgroup (G2 σ Y)}

/- English proof (translation)
Introduce `s hs` and use `by rw [← map_smul, hu s hs, map_zero]`.
-/
theorem at_e {W : Type} [AddCommGroup W] [Module (AF F) W] {ι : Type} (e : W ≃ₗ[AF F] (ι → AF F) × (ι → AF F)) {u : W}
    (hu : At (evI F) u) : At (evI F) (e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hs.pres k, hs.adm k, fun w w' => by simp only [actB, map_add, Matrix.add_mul], fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by have := hs.impl k (dd.e.symm w) φ hφ rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩`.
-/
theorem imp (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) :
    Imp B.ψ (om k) fun w => dd.e (actB (cA σ) k (dd.e.symm w)) :=
  ⟨hs.pres k, hs.adm k, fun w w' => by simp only [actB, map_add, Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := hs.impl k (dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩

/- English proof (translation)
Use `(imp hs k).inter hψ (at_e dd.e hu) hΦ` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem om_D (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) {u} (hu : At (evI F) u) {Φ}
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) : om k (D (dd.e u) Φ) = D (dd.e (actB (cA σ) k u)) (om k Φ) := by
  have := (imp hs k).inter hψ (at_e dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this

/- English proof (translation)
Introduce `s hs` and use `by rw [actB, ← Matrix.smul_mul, hu s hs, Matrix.zero_mul]`.
-/
theorem at_actB (k : G2 σ Y) {u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)} (hu : At (evI F) u) : At (evI F) (actB (cA σ) k u) :=
  fun s hs => by rw [actB, ← Matrix.smul_mul, hu s hs, Matrix.zero_mul]

/- English proof (translation)
Rewrite using `[actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules.
-/
theorem actB_inv (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : actB (cA σ) k (actB (cA σ) k⁻¹ u) = u := by
  rw [actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  simp

variable (om K) in

def kfin : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) where
  carrier := {Φ | ∃ N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ), FiniteDimensional ℂ N ∧ N ≤ schA F _ ∧ Φ ∈ N ∧ ∀ k ∈ K, ∀ Ψ ∈ N, om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩

/- English proof (translation)
Take `⟨N, _, h0, h1, h2⟩` from `h`. Take `⟨N', _, h4⟩` from `exists_D_fin N h0`. Use `⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = D (dd.e v) x}, Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_, Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, -, x, hx, rfl⟩`. Conclude with `h4 _ _ x hx`.

Introduce and unpack `_ ⟨v, -, x, hx, rfl⟩`. Conclude with `DP_mem (h0 hx) _ _`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨v, hv, x, hx, rfl⟩` from `hz`.

Conclude with `Submodule.subset_span ⟨_, at_actB k hv, _, h2 k hk x hx, om_D hψ hs k hv (h0 hx)⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ i j => rw [map_add]`. Conclude with `add_mem i j`.

Consider the case `smul c _ _ i => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ i`.
-/
theorem D_kfin (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {u} (hu : At (evI F) u) {Φ}
    (h : Φ ∈ kfin om K) : D (dd.e u) Φ ∈ kfin om K := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = D (dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, at_actB k hv, _, h2 k hk x hx, om_D hψ hs k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i

abbrev th2 (Y : Spc F E n) (w : InfinitePlace F) := Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w)

/- English proof (translation)
Take `⟨Λ, l1, l2, s, s1, s2⟩` from `hL F E σ B m n A Y hB _ dd K hc Φ hΦ`. Establish `radd : ∀ u (x y : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (x + y) = dd.rho B.ψ u x + dd.rho B.ψ u y` using `fun u x y =>`. Use function extensionality and compare the values at `fun _ => mul_add _ _ _`. Establish `rsmul : ∀ u (c : ℂ) (x : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (c • x) = c • dd.rho B.ψ u x` using `fun u c x =>`. Use function extensionality and compare the values at `fun _ => mul_left_comm _ _ _`.

Set `N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ)` to `{ carrier := {Ψ | Ψ ∈ schA F _ ∧ (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' → Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Ψ = Complex.I • D (dd.e u) Ψ} zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by simp only [D, DP_z …`. Establish `e1` using `h.2.2 u u' a b c`. Establish `e2` using `h'.2.2 u u' a b c`. Simplify using `only [D] at e1 e2 ⊢`. Rewrite using `[DP_add h.1 h'.1, DP_add h.1 h'.1, e1, e2, smul_add]⟩`.

Use the proof step `smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by`. Establish `e1` using `h.2.2 u u' a b c`. Simplify using `only [D] at e1 ⊢`. Rewrite using `[DP_smul h.1, DP_smul h.1, e1, smul_comm]⟩ }`. Use `⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩` and prove the remaining obligations.

Use `FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype) ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))` and prove the remaining obligations. Establish `sp : ∀ x (y : κ ⊕ κ → AF F), (∀ i, evI F (y i) = 0) → pt x 0 + y = pt x (fn y)` using `fun x y hy => by`. Rewrite using `[← pt_self (pt x 0 + y), nf_add, nf_pt, show nf y = 0 from funext hy, add_zero]`. Conclude with `congrArg (pt x) (funext fun i => zero_add _)`. Establish `z0 : ∀ i, evI F (pt 0 (fn z) i) = 0` using `fun i => congrFun (evI_pt 0 (fn z)) i`.

Use `s2 Ψ.1 Ψ.2.2.1 (pt (nf z) 0) (at_pt _) (fun y hy => ?_) _ z0` as an intermediate fact. Rewrite `this` using `[sp _ _ z0, show fn (pt 0 (fn z)) = fn z from rfl, pt_self]`. Then use the resulting hypothesis. Take `⟨f, e⟩` from `slice Ψ.2.1 (fn y)`. Establish `g : Gs dd.e B.emb ε A.θ (th2 Y) f` using `fun u u' a b c => SchwartzMap.ext fun x => by`. Use `congrFun (Ψ.2.2.2 u u' a b c) (pt x (fn y))` as an intermediate fact.

Rewrite `this` using `[Pi.smul_apply, D, D, DP_pt e, DP_pt e]`. Then use the resulting hypothesis. Rewrite using `[sp _ _ (s1 y hy), e]`. Distinguish the cases in `hf : f = 0`. Rewrite using `[hf]`. Both sides reduce to the same expression.

Take `⟨_, hg⟩` from `g.gau hB.cm hf`. Use `(hg.ne 0 ?_).elim` and prove the remaining obligations. Rewrite using `[← e, ← show nf y = 0 from funext (s1 y hy), pt_self]`. Conclude with `congrFun h0 ⟨y, hy⟩`. Rewrite using `[← actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]`.

Rewrite using `[← actB_inv k u, ← actB_inv k u', ← om_D hB.std hs k (at_actB _ a) h.1, ← om_D hB.std hs k (at_actB _ b) h.1, ← map_smul]`. Use `congrArg (om k) (h.2.2 _ _ (at_actB _ a) (at_actB _ b) fun w => ?_)` and prove the remaining obligations. Establish `cm` using `(((hK k⁻¹).1 (inv_mem hk)).1 w).eq`. Simplify using `only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]`. Conclude with `congrArg (fun x => _ • (_ * (_ * xᵀ))) cm`.
-/
theorem vac_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {ε} {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (hv : ∀ u u', At (evI F) u → At (evI F) u' → Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Φ = Complex.I • D (dd.e u) Φ) :
    Φ ∈ kfin om K := by
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := hL F E σ B m n A Y hB _ dd K hc Φ hΦ
  have radd : ∀ u (x y : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (x + y) = dd.rho B.ψ u x + dd.rho B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (c • x) = c • dd.rho B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Ψ = Complex.I • D (dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by simp only [D, DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [D] at e1 e2 ⊢
        rw [DP_add h.1 h'.1, DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [D] at e1 ⊢
        rw [DP_smul h.1, DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : κ ⊕ κ → AF F), (∀ i, evI F (y i) = 0) → pt x 0 + y = pt x (fn y) := fun x y hy => by
      rw [← pt_self (pt x 0 + y), nf_add, nf_pt, show nf y = 0 from funext hy, add_zero]
      exact congrArg (pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (pt 0 (fn z) i) = 0 := fun i => congrFun (evI_pt 0 (fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (pt (nf z) 0) (at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show fn (pt 0 (fn z)) = fn z from rfl, pt_self] at this
    obtain ⟨f, e⟩ := slice Ψ.2.1 (fn y)
    have g : Gs dd.e B.emb ε A.θ (th2 Y) f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (pt x (fn y))
      rwa [Pi.smul_apply, D, D, DP_pt e, DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show nf y = 0 from funext (s1 y hy), pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← actB_inv k u, ← actB_inv k u', ← om_D hB.std hs k (at_actB _ a) h.1, ← om_D hB.std hs k (at_actB _ b) h.1, ← map_smul]
    refine congrArg (om k) (h.2.2 _ _ (at_actB _ a) (at_actB _ b) fun w => ?_)
    have cm := (((hK k⁻¹).1 (inv_mem hk)).1 w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm

/- English proof (translation)
Establish `m1 : pureA F f₁ g₁ ∈ schA F κ` using `Submodule.subset_span ⟨f₁, g₁, s1, rfl⟩`. Establish `m2 : pureA F f₂ g₂ ∈ schA F κ` using `Submodule.subset_span ⟨f₂, g₂, s2, rfl⟩`. Establish `h12 : At (evI F) (Matrix.fromCols u₁ u₂)` using `fun s hs => by`. Use extensionality with `i (j | j)`. Use `exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]`.

Use function extensionality and compare the values at `z`. Establish `a` using `hasD hψ (at_e dd.e h12) (box_mem m1 m2) z`. Establish `a1` using `hasD hψ (at_e d'.e h1) m1 (z ∘ Sum.inl)`. Establish `a2` using `(hasD hψ (at_e d'.e h2) m2 (z ∘ Sum.inr)).star`. Establish `b` using `a1.mul a2`.

Establish `sc0 : ∀ {w}, At (evI F) w → ∀ (Ψ : (κ → AF F) → ℂ) x, schr B.ψ (realAd F 0 • w) Ψ x = Ψ x` using `fun hw Ψ x => by`. Rewrite using `[← pt_self x, schr_pt hψ hw]`. Simplify using `[hl]`. Simplify using `only [sc0 (at_e d'.e h1), sc0 (at_e d'.e h2), D, DP_pure] at b`. Use `a.unique (b.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))` and prove the remaining obligations.

Establish `hb` using `fun s hs => congrArg Prod.snd (at_e d'.e h2 s hs)`. Establish `cj` using `phase_line B.ψ hψ (d'.e u₂).1 (d'.e u₂).2 (z ∘ Sum.inr) hb t`. Establish `cj' : B.ψ (-((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) = star (B.ψ ((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2))))`. Rewrite using `[AddChar.map_neg_eq_inv, cj, ← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]`. Use `congr 1`.

Simplify using `only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hd u₁ u₂, schr, boxFun, Pi.mul_apply, Pi.star_apply, star_mul', Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]`. Rewrite using `[mul_mul_mul_comm, ← cj', ← AddChar.map_add_eq_mul]`. Use `congr 2`.

Simplify using `only [dotProduct, Fintype.sum_sum_type, Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Function.comp_apply, smul_neg, mul_neg, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem D_box (hψ : IsStd B.ψ) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd) {u₁ u₂} (h1 : At (evI F) u₁)
    (h2 : At (evI F) u₂) (f₁ f₂ : SInf F κ) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F)) :
    D (dd.e (Matrix.fromCols u₁ u₂)) (boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂))) =
      boxFun (pureA F (dd0 (d'.e u₁) f₁) g₁) (star (pureA F f₂ g₂)) + boxFun (pureA F f₁ g₁) (star (pureA F (dd0 (d'.e u₂) f₂) g₂)) := by
  have m1 : pureA F f₁ g₁ ∈ schA F κ := Submodule.subset_span ⟨f₁, g₁, s1, rfl⟩
  have m2 : pureA F f₂ g₂ ∈ schA F κ := Submodule.subset_span ⟨f₂, g₂, s2, rfl⟩
  have h12 : At (evI F) (Matrix.fromCols u₁ u₂) := fun s hs => by
    ext i (j | j)
    exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  funext z
  have a := hasD hψ (at_e dd.e h12) (box_mem m1 m2) z
  have a1 := hasD hψ (at_e d'.e h1) m1 (z ∘ Sum.inl)
  have a2 := (hasD hψ (at_e d'.e h2) m2 (z ∘ Sum.inr)).star
  have b := a1.mul a2
  have sc0 : ∀ {w}, At (evI F) w → ∀ (Ψ : (κ → AF F) → ℂ) x, schr B.ψ (realAd F 0 • w) Ψ x = Ψ x := fun hw Ψ x => by
    rw [← pt_self x, schr_pt hψ hw]; simp [hl]
  simp only [sc0 (at_e d'.e h1), sc0 (at_e d'.e h2), D, DP_pure] at b
  refine a.unique (b.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
  have hb := fun s hs => congrArg Prod.snd (at_e d'.e h2 s hs)
  have cj := phase_line B.ψ hψ (d'.e u₂).1 (d'.e u₂).2 (z ∘ Sum.inr) hb t
  have cj' : B.ψ (-((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) =
      star (B.ψ ((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) := by
    rw [AddChar.map_neg_eq_inv, cj, ← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  simp only [hd u₁ u₂, schr, boxFun, Pi.mul_apply, Pi.star_apply, star_mul', Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
  rw [mul_mul_mul_comm, ← cj', ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct, Fintype.sum_sum_type, Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Function.comp_apply,
    smul_neg, mul_neg, Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Set `bx : SInf F κ → SInf F κ → (κ ⊕ κ → AF F) → ℂ` to `fun f f' => boxFun (pureA F f g₁) (star (pureA F f' g₂))`. Establish `z1 : ∀ f', bx 0 f' = 0` using `fun f' => funext fun z => by simp [bx, boxFun, pureA]`. Establish `z2 : ∀ f, bx f 0 = 0` using `fun f => funext fun z => by simp [bx, boxFun, pureA]`. Establish `a1 : ∀ f g f', bx (f + g) f' = bx f f' + bx g f'` using `fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul]`. Establish `a2 : ∀ f f' g, bx f (f' + g) = bx f f' + bx f g` using `fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul, mul_add]`.

Establish `c1 : ∀ (c : ℂ) f f', bx (c • f) f' = c • bx f f'` using `fun c f f' => funext fun z => by simp [bx, boxFun, pureA, mul_assoc]`. Establish `c2 : ∀ (c : ℂ) f f', bx f (c • f') = star c • bx f f'` using `fun c f f' => funext fun z => by`. Simplify using `[bx, boxFun, pureA]`. Expand and normalize the polynomial expressions, which then agree. Establish `at0 : At (evI F) (0 : Matrix (Fin m) (Fin n) (AE F E))` using `fun _ _ => smul_zero _`.

Establish `d0 : ∀ f : SInf F κ, dd0 (d'.e 0) f = 0` using `fun f => SchwartzMap.ext fun x => by`. Simplify using `[dd0, dop_apply, show nf (0 : κ → AF F) = 0 from funext fun _ => evI_zero, linForm_apply]`. Establish `atc : ∀ {u₁ u₂ : Matrix (Fin m) (Fin n) (AE F E)}, At (evI F) u₁ → At (evI F) u₂ → At (evI F) (Matrix.fromCols u₁ u₂)` using `fun h1 h2 s hs => by`. Use extensionality with `i (j | j)`. Use `exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]`.

Establish `base : ∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → ∀ ε' f', Gs d'.e B.emb ε' A.θ Y.θ f' → bx f f' ∈ kfin om K`. Introduce `ε f hf ε' f' hf'`. Distinguish the cases in `e : f = 0`. Rewrite using `[e, z1]`. Conclude with `zero_mem _`.

Distinguish the cases in `e' : f' = 0`. Rewrite using `[e', z2]`. Conclude with `zero_mem _`. Establish `hf''` using `hf.same hB.cm hf' e e'`. Use `vac_kfin (ε := ε) hL hB hK hc hs (box_mem (Submodule.subset_span ⟨f, g₁, s1, rfl⟩) (Submodule.subset_span ⟨f', g₂, s2, rfl⟩)) fun u u' a b c => ?_` and prove the remaining obligations.

Establish `al : ∀ {v : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)}, At (evI F) v → At (evI F) v.toCols₁ ∧ At (evI F) v.toCols₂` using `fun h => ⟨fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inl j), fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inr j)⟩`. Establish `r1 : Rel B.emb ε A.θ Y.θ u.toCols₁ u'.toCols₁` using `fun w => Matrix.ext fun i j => by`. Use `congrFun₂ (c w) i (.inl j)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Establish `r2 : Rel B.emb ε A.θ Y.θ (-u.toCols₂) u'.toCols₂` using `fun w => Matrix.ext fun i j => by`.

Use `congrFun₂ (c w) i (.inr j)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Establish `n2 : dd0 (d'.e (-u.toCols₂)) f' = -dd0 (d'.e u.toCols₂) f'` using `SchwartzMap.ext fun x => by`. Establish `ng : ∀ y : κ → AF F, nf (-y) = -nf y` using `fun y => funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _`. Simplify using `only [dd0, map_neg, Prod.fst_neg, Prod.snd_neg, ng, dop_apply, SchwartzMap.neg_apply, linForm_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← u.fromCols_toCols, ← u'.fromCols_toCols, D_box hB.std hd (al a).1 (al a).2 f f' s1 s2, D_box hB.std hd (al b).1 (al b).2 f f' s1 s2, hf _ _ (al a).1 (al b).1 r1, hf'' _ _ (fun s hs => by rw [smul_neg, (al a).2 s hs, neg_zero]) (al b).2 r2, n2, smul_neg, ← neg_smul]`. Express the relevant statement in the definitionally equal form `bx _ _ + bx _ _ = _ • (bx _ _ + bx _ _)`. Rewrite using `[c1, c2, smul_add]`.

Simplify using the standard rewrite rules. Use `hP ⟨⟨⟨{f' | ∀ f ∈ P, bx f f' ∈ kfin om K}, fun h h' f hf => a2 f _ _ ▸ add_mem (h f hf) (h' f hf)⟩, fun f _ => z2 f ▸ zero_mem _⟩, fun c _ h f hf => c2 c f _ ▸ Submodule.smul_mem _ _ (h f hf)⟩ (fun ε' f' hf' => ?_) (fun u hu f' h f hf => ?_) h2 f₁ h1` and prove the remaining obligations. Use `hP ⟨⟨⟨{f | bx f f' ∈ kfin om K}, fun h h' => by` and prove the remaining obligations. Rewrite using `[Set.mem_setOf_eq, a1]; exact add_mem h h'⟩, by rw [Set.mem_setOf_eq, z1]; exact zero_mem _⟩,`. Use `fun c _ h => by rw [Set.mem_setOf_eq, c1]; exact Submodule.smul_mem _ _ h⟩ (fun ε f hf => base ε f hf ε' f' hf') fun u hu f h => ?_`.

Use `D_kfin hB.std hs (atc hu at0) h` as an intermediate fact. Rewrite `this` using `[D_box hB.std hd hu at0 f f' s1 s2, d0]`. Express the relevant statement in the definitionally equal form `bx _ _ + bx _ _ ∈ _ at this`. Rewrite `this` using `[z2, add_zero]`. Conclude with `this`.

Use `D_kfin hB.std hs (atc at0 hu) (h f hf)` as an intermediate fact. Rewrite `this` using `[D_box hB.std hd at0 hu f f' s1 s2, d0]`. Express the relevant statement in the definitionally equal form `bx _ _ + bx _ _ ∈ _ at this`. Rewrite `this` using `[z1, zero_add]`. Then use the resulting hypothesis.
-/
theorem box_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd)
    {P : Submodule ℂ (SInf F κ)} (hP : ∀ N : Submodule ℂ (SInf F κ), (∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → f ∈ N) →
      (∀ u, At (evI F) u → ∀ f ∈ N, dd0 (d'.e u) f ∈ N) → P ≤ N) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F))
    {f₁ f₂} (h1 : f₁ ∈ P) (h2 : f₂ ∈ P) : boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ kfin om K := by
  let bx : SInf F κ → SInf F κ → (κ ⊕ κ → AF F) → ℂ := fun f f' => boxFun (pureA F f g₁) (star (pureA F f' g₂))
  have z1 : ∀ f', bx 0 f' = 0 := fun f' => funext fun z => by simp [bx, boxFun, pureA]
  have z2 : ∀ f, bx f 0 = 0 := fun f => funext fun z => by simp [bx, boxFun, pureA]
  have a1 : ∀ f g f', bx (f + g) f' = bx f f' + bx g f' := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul]
  have a2 : ∀ f f' g, bx f (f' + g) = bx f f' + bx f g := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul, mul_add]
  have c1 : ∀ (c : ℂ) f f', bx (c • f) f' = c • bx f f' := fun c f f' => funext fun z => by simp [bx, boxFun, pureA, mul_assoc]
  have c2 : ∀ (c : ℂ) f f', bx f (c • f') = star c • bx f f' := fun c f f' => funext fun z => by
    simp [bx, boxFun, pureA]; ring
  have at0 : At (evI F) (0 : Matrix (Fin m) (Fin n) (AE F E)) := fun _ _ => smul_zero _
  have d0 : ∀ f : SInf F κ, dd0 (d'.e 0) f = 0 := fun f => SchwartzMap.ext fun x => by
    simp [dd0, dop_apply, show nf (0 : κ → AF F) = 0 from funext fun _ => evI_zero, linForm_apply]
  have atc : ∀ {u₁ u₂ : Matrix (Fin m) (Fin n) (AE F E)}, At (evI F) u₁ → At (evI F) u₂ → At (evI F) (Matrix.fromCols u₁ u₂) :=
    fun h1 h2 s hs => by
      ext i (j | j)
      exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  have base : ∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → ∀ ε' f', Gs d'.e B.emb ε' A.θ Y.θ f' → bx f f' ∈ kfin om K := by
    intro ε f hf ε' f' hf'
    by_cases e : f = 0
    · rw [e, z1]; exact zero_mem _
    by_cases e' : f' = 0
    · rw [e', z2]; exact zero_mem _
    have hf'' := hf.same hB.cm hf' e e'
    refine vac_kfin (ε := ε) hL hB hK hc hs (box_mem (Submodule.subset_span ⟨f, g₁, s1, rfl⟩) (Submodule.subset_span ⟨f', g₂, s2, rfl⟩))
      fun u u' a b c => ?_
    have al : ∀ {v : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)}, At (evI F) v → At (evI F) v.toCols₁ ∧ At (evI F) v.toCols₂ := fun h =>
      ⟨fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inl j), fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inr j)⟩
    have r1 : Rel B.emb ε A.θ Y.θ u.toCols₁ u'.toCols₁ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inl j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have r2 : Rel B.emb ε A.θ Y.θ (-u.toCols₂) u'.toCols₂ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inr j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have n2 : dd0 (d'.e (-u.toCols₂)) f' = -dd0 (d'.e u.toCols₂) f' := SchwartzMap.ext fun x => by
      have ng : ∀ y : κ → AF F, nf (-y) = -nf y := fun y => funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
      simp only [dd0, map_neg, Prod.fst_neg, Prod.snd_neg, ng, dop_apply, SchwartzMap.neg_apply, linForm_apply, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib]
      push_cast
      ring
    rw [← u.fromCols_toCols, ← u'.fromCols_toCols, D_box hB.std hd (al a).1 (al a).2 f f' s1 s2,
      D_box hB.std hd (al b).1 (al b).2 f f' s1 s2, hf _ _ (al a).1 (al b).1 r1,
      hf'' _ _ (fun s hs => by rw [smul_neg, (al a).2 s hs, neg_zero]) (al b).2 r2, n2, smul_neg, ← neg_smul]
    change bx _ _ + bx _ _ = _ • (bx _ _ + bx _ _)
    rw [c1, c2, smul_add]
    simp
  refine hP ⟨⟨⟨{f' | ∀ f ∈ P, bx f f' ∈ kfin om K}, fun h h' f hf => a2 f _ _ ▸ add_mem (h f hf) (h' f hf)⟩,
    fun f _ => z2 f ▸ zero_mem _⟩, fun c _ h f hf => c2 c f _ ▸ Submodule.smul_mem _ _ (h f hf)⟩ (fun ε' f' hf' => ?_)
    (fun u hu f' h f hf => ?_) h2 f₁ h1
  · refine hP ⟨⟨⟨{f | bx f f' ∈ kfin om K}, fun h h' => by
      rw [Set.mem_setOf_eq, a1]; exact add_mem h h'⟩, by rw [Set.mem_setOf_eq, z1]; exact zero_mem _⟩,
      fun c _ h => by rw [Set.mem_setOf_eq, c1]; exact Submodule.smul_mem _ _ h⟩ (fun ε f hf => base ε f hf ε' f' hf') fun u hu f h => ?_
    have := D_kfin hB.std hs (atc hu at0) h
    rw [D_box hB.std hd hu at0 f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rw [z2, add_zero] at this
    exact this
  · have := D_kfin hB.std hs (atc at0 hu) (h f hf)
    rw [D_box hB.std hd at0 hu f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rwa [z1, zero_add] at this

end GlobalTheory.ThK.Dbl.Box

end
