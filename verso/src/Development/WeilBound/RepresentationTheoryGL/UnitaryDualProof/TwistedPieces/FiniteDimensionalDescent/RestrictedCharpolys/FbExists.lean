import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiA

open PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure FB (k : Type) [Field k] [TopologicalSpace k] (q d : ℕ) where
  β : Fin d → k
  cF : k →+ (Fin d → k)
  recon : ∀ a, ∑ j, cF a j ^ q * β j = a
  uniq : ∀ w : Fin d → k, cF (∑ j, w j ^ q * β j) = w
  cont : Continuous cF

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use `conv_lhs => rw [← B.recon a, Finset.mul_sum]`. Establish `: ∑ j, l ^ q * (B.cF a j ^ q * B.β j) = ∑ j, (l * B.cF a j) ^ q * B.β j` using `Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring`. Rewrite using `[this, B.uniq]`.
-/
theorem fb_smul {q d : ℕ} (B : FB k q d) (l a : k) : B.cF (l ^ q * a) = fun j => l * B.cF a j := by
  conv_lhs => rw [← B.recon a, Finset.mul_sum]
  have : ∑ j, l ^ q * (B.cF a j ^ q * B.β j) = ∑ j, (l * B.cF a j) ^ q * B.β j :=
    Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [this, B.uniq]

/- English proof (translation)
Use `letI := frMod (k := k) p c`. Take `⟨hfd, hpos⟩` from `hF p c`. Use `set d := Module.finrank k (Fr k p c) with hd`. Set `b : Module.Basis (Fin d) k (Fr k p c)` to `Module.finBasis k (Fr k p c)`. Set `toK : Fr k p c → k` to `fun x => x`.

Set `ofK : k → Fr k p c` to `fun x => x`. Establish `hsm : ∀ (a : k) (x : Fr k p c), a • x = ofK (a ^ p ^ c * toK x)`. Introduce `a x`. Use `show iterateFrobenius k p c a * toK x = _`. Rewrite using `[iterateFrobenius_def]`.

Set `β : Fin d → k` to `fun j => toK (b j)`. Set `g : (Fin d → k) → k` to `fun w => ∑ j, w j ^ p ^ c * β j`. Establish `gadd : ∀ v w, g (v + w) = g v + g w`. Introduce `v w`. Simplify using `only [g, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]`.

Set `f : (Fin d → k) →+ k` to `AddMonoidHom.mk' g gadd`. Establish `hfb : ∀ w, f w = toK (b.equivFun.symm w)`. Introduce `w`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Use `show ∑ j, w j ^ p ^ c * β j = _`.

Conclude with `Finset.sum_congr rfl fun j _ => (hsm (w j) (b j)).symm`. Establish `hinj : Function.Injective f`. Introduce `v w h`. Rewrite `h` using `[hfb, hfb]`. Conclude with `b.equivFun.symm.injective h`.

Establish `hsurj : Function.Surjective f`. Introduce `a`. Use `⟨b.equivFun (ofK a), ?_⟩` and prove the remaining obligations. Rewrite using `[hfb, LinearEquiv.symm_apply_apply]`. Establish `hcont : Continuous f` using `by show Continuous g fun_prop`.

Establish `hopen : IsOpenMap f` using `AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hcont`. Set `E : (Fin d → k) ≃+ k` to `AddEquiv.ofBijective f ⟨hinj, hsurj⟩`. Use `⟨d, hpos, ⟨{ β := β, cF := E.symm.toAddMonoidHom, recon := ?_, uniq := ?_, cont := ?_ }⟩⟩` and prove the remaining obligations. Introduce `a`. Conclude with `E.apply_symm_apply a`.

Introduce `w`. Conclude with `E.symm_apply_apply w`. Use `show Continuous E.symm`. Rewrite using `[continuous_def]`. Introduce `U hU`.

Establish `himg : ⇑E.symm ⁻¹' U = f '' U`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨E.symm y, hy, E.apply_symm_apply y⟩`.

Introduce and unpack `⟨x, hx, rfl⟩ show E.symm (E x) ∈ U`. Rewrite using `[E.symm_apply_apply]`. Conclude with `hx`. Rewrite using `[himg]`. Conclude with `hopen U hU`.
-/
theorem fb_exists (hF : FinDim k) (p c : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ d : ℕ, 0 < d ∧ Nonempty (FB k (p ^ c) d) := by
  letI := frMod (k := k) p c
  obtain ⟨hfd, hpos⟩ := hF p c
  set d := Module.finrank k (Fr k p c) with hd
  let b : Module.Basis (Fin d) k (Fr k p c) := Module.finBasis k (Fr k p c)
  let toK : Fr k p c → k := fun x => x
  let ofK : k → Fr k p c := fun x => x
  have hsm : ∀ (a : k) (x : Fr k p c), a • x = ofK (a ^ p ^ c * toK x) := by
    intro a x
    show iterateFrobenius k p c a * toK x = _
    rw [iterateFrobenius_def]
  let β : Fin d → k := fun j => toK (b j)
  let g : (Fin d → k) → k := fun w => ∑ j, w j ^ p ^ c * β j
  have gadd : ∀ v w, g (v + w) = g v + g w := by
    intro v w
    simp only [g, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]
  let f : (Fin d → k) →+ k := AddMonoidHom.mk' g gadd
  have hfb : ∀ w, f w = toK (b.equivFun.symm w) := by
    intro w
    rw [Module.Basis.equivFun_symm_apply]
    show ∑ j, w j ^ p ^ c * β j = _
    exact Finset.sum_congr rfl fun j _ => (hsm (w j) (b j)).symm
  have hinj : Function.Injective f := by
    intro v w h
    rw [hfb, hfb] at h
    exact b.equivFun.symm.injective h
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨b.equivFun (ofK a), ?_⟩
    rw [hfb, LinearEquiv.symm_apply_apply]
  have hcont : Continuous f := by
    show Continuous g
    fun_prop
  have hopen : IsOpenMap f := AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hcont
  let E : (Fin d → k) ≃+ k := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨d, hpos, ⟨{ β := β, cF := E.symm.toAddMonoidHom, recon := ?_, uniq := ?_, cont := ?_ }⟩⟩
  · intro a
    exact E.apply_symm_apply a
  · intro w
    exact E.symm_apply_apply w
  · show Continuous E.symm
    rw [continuous_def]
    intro U hU
    have himg : ⇑E.symm ⁻¹' U = f '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨E.symm y, hy, E.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        show E.symm (E x) ∈ U
        rw [E.symm_apply_apply]
        exact hx
    rw [himg]
    exact hopen U hU

end PositivityTheory.RgUd.TP.Desc.Restr.PphiA
