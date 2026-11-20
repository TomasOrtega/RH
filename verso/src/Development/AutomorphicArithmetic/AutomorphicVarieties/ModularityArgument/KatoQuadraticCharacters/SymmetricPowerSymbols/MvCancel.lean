import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtEx

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m : ℕ}

omit [IsAlgClosure ℚ Ω] in
/- English proof (translation)
Rewrite using `[map_mul, X.sl_mul]`.
-/
private theorem sl_sl (γ δ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
  rw [map_mul, X.sl_mul]

omit [IsAlgClosure ℚ Ω] in
/- English proof (translation)
Rewrite using `[← sl_sl, mul_inv_cancel, map_one, X.sl_one]`.
-/
private theorem sl_inv (γ : SL(2, ℤ)) (f : X.K) : X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) f) = f := by
  rw [← sl_sl, mul_inv_cancel, map_one, X.sl_one]

/- English proof (translation)
Establish `key` using `mvComp Ω ε X m hm (slR X (ofSL γ)) (slR X (ofSL δ)) 1 1 ((admB Ω ε X).1 _) ((admB Ω ε X).1 _) u v P Q R hP hQ hR 1 f h1 h2`. Establish `he : (slR X (ofSL γ)).trans (slR X (ofSL δ)) = slR X (ofSL (γ * δ))`. Use extensionality with `x`. Use `show X.sl (ofSL δ) (X.sl (ofSL γ) x) = X.sl (ofSL (γ * δ)) x`. Conclude with `(sl_sl X γ δ x).symm`.

Rewrite `key` using `[he, mul_one, map_one, one_pow, one_mul]`. Conclude with `key`.
-/
private theorem mv_comp (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R) {f : X.Kˣ}
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL δ)) 1 Q R f) :
    Mv X m (slR X (ofSL (γ * δ))) 1 P R f := by
  have key := mvComp Ω ε X m hm (slR X (ofSL γ)) (slR X (ofSL δ)) 1 1 ((admB Ω ε X).1 _)
    ((admB Ω ε X).1 _) u v P Q R hP hQ hR 1 f h1 h2
  have he : (slR X (ofSL γ)).trans (slR X (ofSL δ)) = slR X (ofSL (γ * δ)) := by
    ext x
    show X.sl (ofSL δ) (X.sl (ofSL γ) x) = X.sl (ofSL (γ * δ)) x
    exact (sl_sl X γ δ x).symm
  rw [he, mul_one, map_one, one_pow, one_mul] at key
  exact key

/- English proof (translation)
Establish `hA` using `admB Ω ε X`. Take `⟨f, -, hf⟩` from `(mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q hQ).1 R hR`. Establish `h3` using `mv_comp X hm γ δ hP hQ hR h1 hf`. Establish `hR' : IsPt X m (X.sl (ofSL (γ * δ)) u) (X.sl (ofSL (γ * δ)) v) R`. Rewrite using `[sl_sl X γ δ u, sl_sl X γ δ v]`.

Conclude with `hR`. Take `⟨k, hk⟩` from `((mvEx Ω ε X m hm (slR X (ofSL (γ * δ))) 1 (hA.1 _) u v P hP).2.2.2 R hR' 1 f h2).mp h3`. Use `((mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q hQ).2.2.2 R hR f 1 hf).mpr ⟨k⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, one_mul, inv_pow, mul_inv_cancel]`.
-/
private theorem mv_cancel (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R)
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL (γ * δ))) 1 P R 1) :
    Mv X m (slR X (ofSL δ)) 1 Q R 1 := by
  have hA := admB Ω ε X
  obtain ⟨f, -, hf⟩ := (mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).1 R hR
  have h3 := mv_comp X hm γ δ hP hQ hR h1 hf
  have hR' : IsPt X m (X.sl (ofSL (γ * δ)) u) (X.sl (ofSL (γ * δ)) v) R := by
    rw [sl_sl X γ δ u, sl_sl X γ δ v]
    exact hR
  obtain ⟨k, hk⟩ := ((mvEx Ω ε X m hm (slR X (ofSL (γ * δ))) 1 (hA.1 _) u v P hP).2.2.2
    R hR' 1 f h2).mp h3
  refine ((mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).2.2.2 R hR f 1 hf).mpr ⟨k⁻¹, ?_⟩
  rw [hk, one_mul, inv_pow, mul_inv_cancel]

omit [IsAlgClosure ℚ Ω] in
/- English proof (translation)
Set `S : Setoid (X.K × X.K)` to `{ r := fun p q => ∃ g : SL(2, ℤ), X.sl (ofSL g) p.1 = q.1 ∧ X.sl (ofSL g) p.2 = q.2 iseqv := ⟨fun p => ⟨1, by rw [map_one, X.sl_one], by rw [map_one, X.sl_one]⟩, fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, sl_inv], by rw [← h2, sl_inv]⟩, fun ⟨g, h1, h2⟩ ⟨k, k1, k2⟩ => ⟨g * k, by rw [sl …`. Use `⟨fun p => (Quotient.mk S p).out, fun p => Classical.choose (Quotient.mk_out (s := S) p), fun p => Classical.choose_spec (Quotient.mk_out (s := S) p), fun p γ => ?_⟩` and prove the remaining obligations. Use `show (Quotient.mk S _).out = (Quotient.mk S p).out`. Rewrite using `[Quotient.sound (s := S) ⟨γ⁻¹, sl_inv X γ p.1, sl_inv X γ p.2⟩]`.
-/
private theorem rep_ex : ∃ (r : X.K × X.K → X.K × X.K) (g : X.K × X.K → SL(2, ℤ)),
    (∀ p, X.sl (ofSL (g p)) (r p).1 = p.1 ∧ X.sl (ofSL (g p)) (r p).2 = p.2) ∧
    ∀ (p : X.K × X.K) (γ : SL(2, ℤ)), r (X.sl (ofSL γ) p.1, X.sl (ofSL γ) p.2) = r p := by
  let S : Setoid (X.K × X.K) :=
    { r := fun p q => ∃ g : SL(2, ℤ), X.sl (ofSL g) p.1 = q.1 ∧ X.sl (ofSL g) p.2 = q.2
      iseqv := ⟨fun p => ⟨1, by rw [map_one, X.sl_one], by rw [map_one, X.sl_one]⟩,
        fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, sl_inv], by rw [← h2, sl_inv]⟩,
        fun ⟨g, h1, h2⟩ ⟨k, k1, k2⟩ => ⟨g * k, by rw [sl_sl, h1, k1], by rw [sl_sl, h2, k2]⟩⟩ }
  refine ⟨fun p => (Quotient.mk S p).out, fun p => Classical.choose (Quotient.mk_out (s := S) p),
    fun p => Classical.choose_spec (Quotient.mk_out (s := S) p), fun p γ => ?_⟩
  show (Quotient.mk S _).out = (Quotient.mk S p).out
  rw [Quotient.sound (s := S) ⟨γ⁻¹, sl_inv X γ p.1, sl_inv X γ p.2⟩]

end

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm`. Take `⟨r, g, hg, hr⟩` from `rep_ex X`. Establish `hA` using `admB Ω ε X`. Use `haveI : Nonempty (Pt X m) := ⟨⟨0, 0, fun _ => 0⟩⟩`. Establish `hUsl : ∀ (γ : SL(2, ℤ)) (a : X.K), IsU X a → IsU X (X.sl (ofSL γ) a)` using `fun γ a ha => (hA.2.2.2.2.2.1 _ _ (hA.1 (ofSL γ))).1 a ha`.

Set `Good : X.K → X.K → Pt X m → Prop` to `fun a b P => IsPt X m a b P ∧ ∀ γ : SL(2, ℤ), X.sl (ofSL γ) a = a → X.sl (ofSL γ) b = b → Mv X m (slR X (ofSL γ)) 1 P P 1`. Set `P0 : X.K → X.K → Pt X m` to `fun a b => Classical.epsilon (Good a b)`. Establish `hP0 : ∀ a b, IsU X a → IsU X b → Good a b (P0 a b)` using `fun a b ha hb => Classical.epsilon_spec (ptEx Ω ε X m hm a b ha hb)`. Establish `hrep : ∀ a b, X.sl (ofSL (g (a, b))) (r (a, b)).1 = a ∧ X.sl (ofSL (g (a, b))) (r (a, b)).2 = b` using `fun a b => hg (a, b)`. Establish `hrU : ∀ a b, IsU X a → IsU X b → IsU X (r (a, b)).1 ∧ IsU X (r (a, b)).2`.

Introduce `a b ha hb`. Establish `e1` using `congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).1`. Establish `e2` using `congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).2`. Simplify using `only [sl_inv] at e1 e2`. Rewrite using `[e1, e2]`.

Conclude with `⟨hUsl _ a ha, hUsl _ b hb⟩`. Set `t : X.K → X.K → Pt X m` to `fun a b => Classical.epsilon (fun Q => IsPt X m a b Q ∧ Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1)`. Establish `ht : ∀ a b, IsU X a → IsU X b → IsPt X m a b (t a b) ∧ Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) (t a b) 1`. Introduce `a b ha hb`. Take `⟨h1, h2⟩` from `hrU a b ha hb`.

Take `⟨Q, hQ, hM⟩` from `(mvEx Ω ε X m hm (slR X (ofSL (g (a, b)))) 1 (hA.1 _) _ _ _ (hP0 _ _ h1 h2).1).2.1`. Express the relevant statement in the definitionally equal form `IsPt X m (X.sl (ofSL (g (a, b))) (r (a, b)).1) (X.sl (ofSL (g (a, b))) (r (a, b)).2) Q at hQ`. Rewrite `hQ` using `[(hrep a b).1, (hrep a b).2]`. Conclude with `Classical.epsilon_spec (p := fun Q => IsPt X m a b Q ∧ Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1) ⟨Q, hQ, hM⟩`. Use `⟨t, fun u v hu hv => ⟨(ht u v hu hv).1, fun γ => ?_⟩⟩` and prove the remaining obligations.

Establish `hu'` using `hUsl γ u hu`. Establish `hv'` using `hUsl γ v hv`. Establish `hrr : r (X.sl (ofSL γ) u, X.sl (ofSL γ) v) = r (u, v)` using `hr (u, v) γ`. Take `⟨hQt, hMa⟩` from `ht u v hu hv`. Take `⟨hRt, hMb⟩` from `ht _ _ hu' hv'`.

Take `⟨q1, q2⟩` from `hrU u v hu hv`. Establish `hgood` using `hP0 _ _ q1 q2`. Take `⟨e1, e2⟩` from `hrep u v`. Take `⟨f1, f2⟩` from `hrep (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)`. Rewrite `hMb`, `f1`, `f2` using `[hrr]`.

Establish `hs1 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).1 = (r (u, v)).1`. Rewrite using `[sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e1]`. Establish `k` using `sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).1`. Rewrite `k` using `[f1]`. Conclude with `k`.

Establish `hs2 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).2 = (r (u, v)).2`. Rewrite using `[sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e2]`. Establish `k` using `sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).2`. Rewrite `k` using `[f2]`. Conclude with `k`.

Establish `stab` using `hgood.2 _ hs1 hs2`. Establish `comp` using `mv_comp X hm _ (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) hgood.1 (by rw [hs1, hs2]; exact hgood.1) (by rw [hs1, hs2, f1, f2]; exact hRt) stab hMb`. Rewrite `comp` using `[inv_mul_cancel_right]`. Conclude with `mv_cancel X hm (g (u, v)) γ hgood.1 (by rw [e1, e2]; exact hQt) (by rw [e1, e2]; exact hRt) hMa comp`.
-/
theorem UpperTheory.V.Z.Kato.Sym.secEx :
    UpperTheory.V.Z.Kato.Sym.SecEx := by
  intro Ω _ _ _ ε X m hm
  obtain ⟨r, g, hg, hr⟩ := rep_ex X
  have hA := admB Ω ε X
  haveI : Nonempty (Pt X m) := ⟨⟨0, 0, fun _ => 0⟩⟩
  have hUsl : ∀ (γ : SL(2, ℤ)) (a : X.K), IsU X a → IsU X (X.sl (ofSL γ) a) :=
    fun γ a ha => (hA.2.2.2.2.2.1 _ _ (hA.1 (ofSL γ))).1 a ha
  let Good : X.K → X.K → Pt X m → Prop := fun a b P => IsPt X m a b P ∧
    ∀ γ : SL(2, ℤ), X.sl (ofSL γ) a = a → X.sl (ofSL γ) b = b → Mv X m (slR X (ofSL γ)) 1 P P 1
  let P0 : X.K → X.K → Pt X m := fun a b => Classical.epsilon (Good a b)
  have hP0 : ∀ a b, IsU X a → IsU X b → Good a b (P0 a b) :=
    fun a b ha hb => Classical.epsilon_spec (ptEx Ω ε X m hm a b ha hb)
  have hrep : ∀ a b, X.sl (ofSL (g (a, b))) (r (a, b)).1 = a ∧
      X.sl (ofSL (g (a, b))) (r (a, b)).2 = b := fun a b => hg (a, b)
  have hrU : ∀ a b, IsU X a → IsU X b → IsU X (r (a, b)).1 ∧ IsU X (r (a, b)).2 := by
    intro a b ha hb
    have e1 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).1
    have e2 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).2
    simp only [sl_inv] at e1 e2
    rw [e1, e2]
    exact ⟨hUsl _ a ha, hUsl _ b hb⟩
  let t : X.K → X.K → Pt X m := fun a b => Classical.epsilon (fun Q => IsPt X m a b Q ∧
    Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1)
  have ht : ∀ a b, IsU X a → IsU X b → IsPt X m a b (t a b) ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) (t a b) 1 := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := hrU a b ha hb
    obtain ⟨Q, hQ, hM⟩ := (mvEx Ω ε X m hm (slR X (ofSL (g (a, b)))) 1 (hA.1 _) _ _ _
      (hP0 _ _ h1 h2).1).2.1
    change IsPt X m (X.sl (ofSL (g (a, b))) (r (a, b)).1)
      (X.sl (ofSL (g (a, b))) (r (a, b)).2) Q at hQ
    rw [(hrep a b).1, (hrep a b).2] at hQ
    exact Classical.epsilon_spec (p := fun Q => IsPt X m a b Q ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1) ⟨Q, hQ, hM⟩
  refine ⟨t, fun u v hu hv => ⟨(ht u v hu hv).1, fun γ => ?_⟩⟩
  have hu' := hUsl γ u hu
  have hv' := hUsl γ v hv
  have hrr : r (X.sl (ofSL γ) u, X.sl (ofSL γ) v) = r (u, v) := hr (u, v) γ
  obtain ⟨hQt, hMa⟩ := ht u v hu hv
  obtain ⟨hRt, hMb⟩ := ht _ _ hu' hv'
  obtain ⟨q1, q2⟩ := hrU u v hu hv
  have hgood := hP0 _ _ q1 q2
  obtain ⟨e1, e2⟩ := hrep u v
  obtain ⟨f1, f2⟩ := hrep (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)
  rw [hrr] at hMb f1 f2
  have hs1 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).1
      = (r (u, v)).1 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e1]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).1
    rw [f1] at k
    exact k
  have hs2 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).2
      = (r (u, v)).2 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e2]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).2
    rw [f2] at k
    exact k
  have stab := hgood.2 _ hs1 hs2
  have comp := mv_comp X hm _ (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) hgood.1
    (by rw [hs1, hs2]; exact hgood.1) (by rw [hs1, hs2, f1, f2]; exact hRt) stab hMb
  rw [inv_mul_cancel_right] at comp
  exact mv_cancel X hm (g (u, v)) γ hgood.1 (by rw [e1, e2]; exact hQt)
    (by rw [e1, e2]; exact hRt) hMa comp
