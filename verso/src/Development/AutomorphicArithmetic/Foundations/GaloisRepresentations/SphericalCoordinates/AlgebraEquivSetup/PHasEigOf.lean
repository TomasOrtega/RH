import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Establish `hfin` using `Formalism.UG.P.finite_supp K hK f hf`. Unfold `hAct`. Rewrite using `[map_finsum L (hfin.subset (fun x hx => by`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `[h0]))]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[map_smul, mul_assoc]`.
-/
private theorem hAct_slice {X V : Type} [Group X] [AddCommGroup V] [Module ℂ V] (K : Subgroup X)
    (hK : IsCommensurated K) (f : X → ℂ) (hf : f ∈ Hecke ℂ K) (φ : X → V) (L : V →ₗ[ℂ] V) (a g : X) :
    hAct K f (fun x => L (φ (a * x))) g = L (hAct K f φ (a * g)) := by
  have hfin := Formalism.UG.P.finite_supp K hK f hf
  unfold hAct
  rw [map_finsum L (hfin.subset (fun x hx => by
    intro h0; apply hx; simp [h0]))]
  refine finsum_congr fun x => ?_
  rw [map_smul, mul_assoc]

/- English proof (translation)
Unfold `UpperTheory.Gal.Spc.op hAct`. Use `finsum_congr fun h => ?_` and prove the remaining obligations. Simplify using `[Prod.mk_mul_mk]`.
-/
private theorem op_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V : Type} [AddCommGroup V] [Module ℂ V]
    (K : Subgroup G.GAf) (f : G.GAf → ℂ) (F : G.GAf × Gr G 1 → V) (g : G.GAf) (g₂ : Gr G 1) :
    UpperTheory.Gal.Spc.op K f F (g, g₂) = hAct K f (fun x => F (x, g₂)) g := by
  unfold UpperTheory.Gal.Spc.op hAct
  refine finsum_congr fun h => ?_
  simp [Prod.mk_mul_mk]

/- English proof (translation)
Use function extensionality and compare the values at `⟨g, g₂⟩`. Rewrite using `[op_eq]`. Break down `hF g₂ with h0 | ⟨γ, hγ⟩` into its components or cases. Establish `e : (fun x => F (x, g₂)) = fun _ => 0` using `funext h0`. Rewrite using `[e]`.

Simplify using `[hAct, h0]`. Establish `e : (fun x => F (x, g₂)) = fun x => ξ' γ (φ ((ι γ).1⁻¹ * x))` using `funext hγ`. Rewrite using `[e, hAct_slice K hK f hf, h]`. Simplify using `[hγ]`.
-/
private theorem op_eig {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
    (ι : Γ →* G.GAf × Gr G 1) (K : Subgroup G.GAf) (hK : IsCommensurated K) (ξ' : Representation ℂ Γ V)
    (φ : G.GAf → V) (F : G.GAf × Gr G 1 → V)
    (hF : ∀ g₂ : Gr G 1, (∀ g, F (g, g₂) = 0) ∨ ∃ γ, ∀ g, F (g, g₂) = ξ' γ (φ ((ι γ).1⁻¹ * g)))
    (f : G.GAf → ℂ) (hf : f ∈ Hecke ℂ K) (c : ℂ) (h : hAct K f φ = c • φ) :
    UpperTheory.Gal.Spc.op K f F = c • F := by
  funext ⟨g, g₂⟩
  rw [op_eq]
  rcases hF g₂ with h0 | ⟨γ, hγ⟩
  · have e : (fun x => F (x, g₂)) = fun _ => 0 := funext h0
    rw [e]
    simp [hAct, h0]
  · have e : (fun x => F (x, g₂)) = fun x => ξ' γ (φ ((ι γ).1⁻¹ * x)) := funext hγ
    rw [e, hAct_slice K hK f hf, h]
    simp [hγ]

end UpperTheory.Gal.W2.Seed

/- English proof (translation)
Introduce `hStd hPI hPP hExt E _ _ _ A n p _ S T V _ _ ξ Φ hΦL hΦR hΦ0 K₀ hK₀ hK₀inv J ψ θ e hψ he heΦ hψΦ`. Take `⟨B, x, hx, ee, hee, hemb⟩` from `hStd E A n p S T`. Set `ξ' : Representation ℂ (S.G.Cˣ × ℚˣ) V` to `ξ`. Set `ξ₀ : Representation ℂ (GlobalTheory.LKCx.grp S.G B.β) V` to `ξ'.comp (GlobalTheory.LKCx.grp S.G B.β).subtype`. Set `φ : S.G.GAf → V` to `fun h => Φ (T.sec h)`.

Establish `hEq : ∀ γ : GlobalTheory.LKCx.grp S.G B.β, (B.embAt x 1 hx γ).2 ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G → ∀ g, φ ((B.embAt x 1 hx γ).1 * g) = ξ₀ γ (φ g)`. Introduce `γ hγ g`. Establish `h1 : (B.embAt x 1 hx γ).1 = T.j (rat (ee γ))` using `hemb γ`. Establish `hy : inclG S.G 1 (locC S.G ((ee γ : Gam0 E n) : GL (Fin n) E × ℚˣ)) ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G`. Rewrite using `[hee]`.

Conclude with `hγ`. Take `⟨hI, -⟩` from `hPI E A n p S (ee γ) hy`. Take `⟨k, hk, hk1, hk2, hk3⟩` from `hPP E A n p S T (rat (ee γ))`. Establish `hsec : T.sec (T.j (rat (ee γ))) = rat (ee γ) * k⁻¹` using `eq_mul_inv_of_mul_eq hk.symm`. Establish `hc : k⁻¹ * T.sec g = T.sec g * k⁻¹`.

Rewrite using `[eq_mul_inv_iff_mul_eq, mul_assoc, hk3 g, inv_mul_cancel_left]`. Establish `hR : ∀ g', Φ (g' * k⁻¹) = Φ g'` using `hΦR k⁻¹ (fun w hw => by rw [map_inv, hk1 w hw, inv_one]) (fun w hw => by rw [map_inv]; exact inv_mem (by rw [hk2 w hw]; exact hI w hw))`. Use `show Φ (T.sec ((B.embAt x 1 hx γ).1 * g)) = ξ₀ γ (Φ (T.sec g))`. Rewrite using `[h1, map_mul, hsec, mul_assoc, hc, hΦL, hR, hee]`. Both sides reduce to the same expression.

Take `⟨F, hF1, hF2⟩` from `hExt (GlobalTheory.LKCx.grp S.G B.β) S.G.GAf (Gr S.G 1) V (B.embAt x 1 hx) K₀ (UpperTheory.Gal.LocalSmoothExtension.Kp S.G) ξ₀ φ hEq (fun k hk g => hK₀inv k hk g)`. Establish `hne : F ≠ 0`. Take `⟨g₀, hg₀, hg₀p⟩` from `hΦ0`. Take `⟨k, hk, hk1, hk2, -⟩` from `hPP E A n p S T g₀`. Establish `h2 : Φ g₀ = φ (T.j g₀)`.

Combine the equalities or inequalities in the displayed calculation. Introduce `h0`. Apply `hg₀` to reduce the goal to its premises. Rewrite using `[h2, ← hF1, h0]`. Both sides reduce to the same expression.

Use `⟨B, x, 1, hx, (F : S.G.GAf × Gr S.G 1 → V), F.2, ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hne (Subtype.ext h0)`. Use `op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 e he 1 (by simpa using heΦ)` as an intermediate fact. Simplify using `using this`.

Conclude with `op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 (ψ j) (hψ j) (θ j) (hψΦ j)`.
-/
theorem UpperTheory.Gal.W2.Seed.pHasEigOf :
    StdForm → PInt → PPart → ExtP → HasEigOf := by
  intro hStd hPI hPP hExt E _ _ _ A n p _ S T V _ _ ξ Φ hΦL hΦR hΦ0 K₀ hK₀ hK₀inv J ψ θ e hψ he heΦ hψΦ
  obtain ⟨B, x, hx, ee, hee, hemb⟩ := hStd E A n p S T
  let ξ' : Representation ℂ (S.G.Cˣ × ℚˣ) V := ξ
  let ξ₀ : Representation ℂ (GlobalTheory.LKCx.grp S.G B.β) V := ξ'.comp (GlobalTheory.LKCx.grp S.G B.β).subtype
  let φ : S.G.GAf → V := fun h => Φ (T.sec h)
  have hEq : ∀ γ : GlobalTheory.LKCx.grp S.G B.β, (B.embAt x 1 hx γ).2 ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G → ∀ g,
      φ ((B.embAt x 1 hx γ).1 * g) = ξ₀ γ (φ g) := by
    intro γ hγ g
    have h1 : (B.embAt x 1 hx γ).1 = T.j (rat (ee γ)) := hemb γ
    have hy : inclG S.G 1 (locC S.G ((ee γ : Gam0 E n) : GL (Fin n) E × ℚˣ)) ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G := by
      rw [hee]; exact hγ
    obtain ⟨hI, -⟩ := hPI E A n p S (ee γ) hy
    obtain ⟨k, hk, hk1, hk2, hk3⟩ := hPP E A n p S T (rat (ee γ))
    have hsec : T.sec (T.j (rat (ee γ))) = rat (ee γ) * k⁻¹ := eq_mul_inv_of_mul_eq hk.symm
    have hc : k⁻¹ * T.sec g = T.sec g * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hk3 g, inv_mul_cancel_left]
    have hR : ∀ g', Φ (g' * k⁻¹) = Φ g' := hΦR k⁻¹
      (fun w hw => by rw [map_inv, hk1 w hw, inv_one])
      (fun w hw => by rw [map_inv]; exact inv_mem (by rw [hk2 w hw]; exact hI w hw))
    show Φ (T.sec ((B.embAt x 1 hx γ).1 * g)) = ξ₀ γ (Φ (T.sec g))
    rw [h1, map_mul, hsec, mul_assoc, hc, hΦL, hR, hee]
    rfl
  obtain ⟨F, hF1, hF2⟩ := hExt (GlobalTheory.LKCx.grp S.G B.β) S.G.GAf (Gr S.G 1) V (B.embAt x 1 hx) K₀
    (UpperTheory.Gal.LocalSmoothExtension.Kp S.G) ξ₀ φ hEq (fun k hk g => hK₀inv k hk g)
  have hne : F ≠ 0 := by
    obtain ⟨g₀, hg₀, hg₀p⟩ := hΦ0
    obtain ⟨k, hk, hk1, hk2, -⟩ := hPP E A n p S T g₀
    have h2 : Φ g₀ = φ (T.j g₀) := by
      calc Φ g₀ = Φ (T.sec (T.j g₀) * k) := congrArg Φ hk
        _ = φ (T.j g₀) := hΦR k hk1 (fun w hw => by rw [hk2 w hw]; exact hg₀p w hw) _
    intro h0
    apply hg₀
    rw [h2, ← hF1, h0]
    rfl
  refine ⟨B, x, 1, hx, (F : S.G.GAf × Gr S.G 1 → V), F.2, ?_, ?_, fun j => ?_⟩
  · intro h0
    exact hne (Subtype.ext h0)
  · have := op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 e he 1 (by simpa using heΦ)
    simpa using this
  · exact op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 (ψ j) (hψ j) (θ j) (hψΦ j)
