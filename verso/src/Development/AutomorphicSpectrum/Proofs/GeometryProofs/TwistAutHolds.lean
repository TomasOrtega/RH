import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistInverseIsoStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistIsoNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ObjMapCompStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistObjMapFunctorialStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAllStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliTwistAutomorphismStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReducedStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TwistAutProof

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
The claim follows from `(Xo.rep S s' hS o).unique ⟨h₁, ⟨m₁⟩⟩ ⟨h₂, ⟨m₂⟩⟩`.
-/
theorem eq_of_objMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) {S : Scheme.{0}} (s' : S ⟶ Sp (KA l)) (hS : IsReduced S) (o : Obj D l (baseKA l) s')
    (f₁ f₂ : S ⟶ Xo.X) (h₁ : f₁ ≫ Xo.s = s') (h₂ : f₂ ≫ Xo.s = s') (m₁ : ObjMap o Xo.univ f₁)
    (m₂ : ObjMap o Xo.univ f₂) : f₁ = f₂ :=
  (Xo.rep S s' hS o).unique ⟨h₁, ⟨m₁⟩⟩ ⟨h₂, ⟨m₂⟩⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo g`. Use `⟨GlobalTheory.T.twist_iso_nonempty E H D g, fun a => ?_⟩` and prove the remaining obligations. Establish `hred : IsReduced Xo.X` using `GlobalTheory.T.isReduced_moduli' E H D l Xo`. Take `⟨a', hback⟩` from `GlobalTheory.T.twist_inverse_iso E H D g a`. Establish `h : TwOK Xo.univ g a` using `GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g a`.

Establish `h' : TwOK Xo.univ g.symm a'` using `GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g.symm a'`. Take `⟨Φ, hΦ, ⟨m⟩⟩` from `GlobalTheory.T.moduli_twist_automorphism E H D l Xo g a h`. Take `⟨Ψ, hΨ, ⟨m'⟩⟩` from `GlobalTheory.T.moduli_twist_automorphism E H D l Xo g.symm a' h'`. Take `⟨back₁, back₂⟩` from `hback l _ (baseKA l) Xo.X Xo.s Xo.univ`. Establish `e₁ : Φ ≫ Ψ = 𝟙 Xo.X`.

Establish `k : TwOK (twistObj Xo.univ g a h) g.symm a'` using `GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g.symm a'`. Take `⟨n, -⟩` from `GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Φ m g.symm a' h' k`. Take `⟨n', -⟩` from `GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Ψ Φ m' n`. Take `⟨i⟩` from `back₁ h k`. Conclude with `eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΨ, hΦ]) (Category.id_comp _) n' i`.

Establish `e₂ : Ψ ≫ Φ = 𝟙 Xo.X`. Establish `k : TwOK (twistObj Xo.univ g.symm a' h') g a` using `GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g a`. Take `⟨n, -⟩` from `GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Ψ m' g a h k`. Take `⟨n', -⟩` from `GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Φ Ψ m n`. Take `⟨i⟩` from `back₂ h' k`.

Conclude with `eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΦ, hΨ]) (Category.id_comp _) n' i`. Conclude with `⟨h, ⟨Φ, Ψ, e₁, e₂⟩, hΦ, ⟨m⟩⟩`.
-/
theorem twistAut : TwistAut := by
  intro E _ _ _ H D l Xo g
  refine ⟨GlobalTheory.T.twist_iso_nonempty E H D g, fun a => ?_⟩
  have hred : IsReduced Xo.X := GlobalTheory.T.isReduced_moduli' E H D l Xo
  obtain ⟨a', hback⟩ := GlobalTheory.T.twist_inverse_iso E H D g a
  have h : TwOK Xo.univ g a := GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g a
  have h' : TwOK Xo.univ g.symm a' := GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g.symm a'
  obtain ⟨Φ, hΦ, ⟨m⟩⟩ := GlobalTheory.T.moduli_twist_automorphism E H D l Xo g a h
  obtain ⟨Ψ, hΨ, ⟨m'⟩⟩ := GlobalTheory.T.moduli_twist_automorphism E H D l Xo g.symm a' h'
  obtain ⟨back₁, back₂⟩ := hback l _ (baseKA l) Xo.X Xo.s Xo.univ

  have e₁ : Φ ≫ Ψ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g a h) g.symm a' :=
      GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g.symm a'
    obtain ⟨n, -⟩ := GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Φ m g.symm a' h' k
    obtain ⟨n', -⟩ := GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Ψ Φ m' n
    obtain ⟨i⟩ := back₁ h k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΨ, hΦ]) (Category.id_comp _) n' i

  have e₂ : Ψ ≫ Φ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g.symm a' h') g a :=
      GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g a
    obtain ⟨n, -⟩ := GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Ψ m' g a h k
    obtain ⟨n', -⟩ := GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Φ Ψ m n
    obtain ⟨i⟩ := back₂ h' k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΦ, hΨ]) (Category.id_comp _) n' i
  exact ⟨h, ⟨Φ, Ψ, e₁, e₂⟩, hΦ, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.TwistAutProof
