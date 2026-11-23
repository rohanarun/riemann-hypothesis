module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain

namespace GlobalTheory.CoefDuty

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}

def Built (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (AutSpec A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)

def ExtOf (L₀ L₁ : LocAll (lay0 D)) (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc) : Prop :=
  L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧
    Nonempty (LocExt L₀.lay.fixZ.nd L₁.lay.fixZ.nd L₀.lay.fixZ.naut L₁.lay.fixZ.naut i₀ i₁)

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolyEqOfIsRowPar
section
noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

variable {D : D7}

theorem mem_plB (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    Pl.ι w (z : Qbar (D.what₂.places.resChar w)) ∈ Pl.plB w := by
  rw [Pl.plB_eq, RingEquiv.symm_apply_apply]
  exact z.2

def plRed (Pl : PlSide D) (w : D.what₂.places.Pl) : Zbar (D.what₂.places.resChar w) →+* FbAt D w :=
  ((Pl.plκ w).toRingHom.comp (IsLocalRing.residue (Pl.plB w))).comp
    (((Pl.ι w).toRingHom.comp (Zbar (D.what₂.places.resChar w)).subtype).codRestrict (Pl.plB w) (mem_plB Pl w))

theorem plRed_eq (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    plRed Pl w z = Formalism.L2.NT.redThrough (Pl.plB w) (Pl.plκ w) (Pl.ι w z) := by
  rw [Formalism.L2.NT.redThrough, dite_eq_left (mem_plB Pl w z)]
  rfl

theorem teichAt_of_iotaOk {Pl : PlSide D} (h : IotaOk D Pl) (w : D.what₂.places.Pl) : TeichAt (Pl.ι w) w (plRed Pl w) :=
  fun k _ v x _ z hz => by rw [plRed_eq, hz, RingEquiv.apply_symm_apply, h]

theorem resTied_of_plSide {Rw : RowSide D} {Pl : PlSide D} (h : IotaOk D Pl)
    (hr : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ σ π r, D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π _ (Pl.ι w) r → IsSSRep (D.ntypes.rbar σ w) ∧ ∀ g, ∃ p : (Zbar (D.what₂.places.resChar w))[X],
        p.map (Zbar (D.what₂.places.resChar w)).subtype = ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar w))).charpoly ∧
        p.map (plRed Pl w) =
          ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) :
    ResTied D Rw := by
  intro w hw l _ e
  subst e
  exact ⟨Pl.ι w, plRed Pl w, Pl.ι_w w, teichAt_of_iotaOk h w, fun σ π r h1 h2 h3 h4 =>
    ⟨(hr w hw σ π r h1 h2 h3 h4).1, (hr w hw σ π r h1 h2 h3 h4).2, teichAt_of_iotaOk h w⟩⟩

end GlobalTheory.EigTie

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.TypeRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

structure Ident (D : D7) where
  i : ∀ (k : Fin 2) (v : D.nd.PlG k), ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E
  cont : ∀ k v, Continuous (i k v)

def pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) :
    Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]) :=
  Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom))

def IsRc (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D)
    (rc : GlobalTheory.SerSys.Corr D) : Prop :=
  ∀ k v n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])), Nonempty (π ≅ pull I k v σ) →
    T.e _ (rc k v n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)

def IsComp {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D) : Prop :=
  ∀ σ k v, ∃ (s : SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ cp σ k v = pull I k v τ

end GlobalTheory.TypeRec

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
section
noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

def EigTrue (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ (j : Fin D.R.m) σ, D.what₂.isot (j.1 + 1) σ ≠ ⊥ → D.nd.goodRow σ → ∀ P, IsSplitPl D.host P → P ∉ Sb →
    D.naut.unr (Rw.locR σ P) ∧ ∀ k, 1 ≤ k → k ≤ D.R.r → D.what₂.embLL (eig (j.1 + 1) σ k P : D.what₂.LL) =
      ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * ((D.naut.frobEig (Rw.locR σ P)).map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k

def EigOcc (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ x ∈ goodL D S θ j, x ≠ 0 ∧
    ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ Sb → hL j k P x = ((eig j σ k P : ↥D.LL0) : D.what₂.LL) • x

def RowParam (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π, GlobalTheory.EigTie.IsRowPar Rw σ π

def NoFormsOff (D : D7) : Prop := ∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)

def MeetsAll (D : D7) : Prop := ∀ i j b (W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)), W ≠ ⊥ →
  GStable D.nexp i j b W → (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

def CommAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ g x,
  D.nexp.hkF i j b k P (D.nexp.actG i j b g x) = D.nexp.actG i j b g (D.nexp.hkF i j b k P x)

def FullAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

end GlobalTheory.TwInputs

end
end

