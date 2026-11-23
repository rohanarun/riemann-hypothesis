module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.LubinTateReciprocity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitary

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : AL L) :
    compAt L v (conjAL L a) = Formalism.UG.sigR (↑(IsCMField.complexConj L))
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v) (compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [compAt, conjAL, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m]
    (M N : Matrix m m A) : Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m] :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  unfold Formalism.UG.cT
  simp

theorem cT_conj_form {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]
    (Pm Pi X : Matrix m m A) (h1 : Pm * Pi = 1) (hX : Formalism.UG.cT σ X * X = 1) :
    Formalism.UG.cT σ (Pi * X * Pm) * (Formalism.UG.cT σ Pm * Pm) * (Pi * X * Pm) = Formalism.UG.cT σ Pm * Pm := by
  have h2 : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by
    rw [← cT_mul, h1, cT_one]
  rw [cT_mul, cT_mul]
  calc _ = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ X * ((Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm) * ((Pm * Pi) * X))) * Pm := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Pm * Pm := by
        rw [h1, h2, Matrix.one_mul, Matrix.one_mul, hX, Matrix.mul_one]

theorem mem_UJ_iff {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m] (σ : A →+* A)
    (J : Matrix m m A) (g : GL m A) : g ∈ Formalism.UG.UJ σ J ↔ Formalism.UG.cT σ (g : Matrix m m A) * J * g = J := Iff.rfl

theorem loc_mem_GU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  intro L _ _ _ n v w Dv x
  let φ : AL L →+* HeightOneSpectrum.adicCompletion L w :=
    (Dv.e : _ →+* HeightOneSpectrum.adicCompletion L w).comp (compAt L v)
  have hφ : ∀ a : AL L, φ (conjAL L a) = Dv.σw (φ a) := by
    intro a
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe, compAt_conjAL, Dv.comm]
  have hx : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ReciprocityTheory.Aut.conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hconj : φ.mapMatrix (ReciprocityTheory.Aut.conjT (conjAL L)
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) =
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ReciprocityTheory.Aut.conjT, Formalism.UG.cT,
      Matrix.transpose_apply, hφ]
  have hX : φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) = 1 := by
    rw [← hconj, ← map_mul, hx, map_one]
  have hX' := mul_eq_one_comm.mp hX
  have hloc : ((Dv.loc x : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
      Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) =
      ((Dv.P⁻¹ : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) *
      φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((Dv.P : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) := by
    rw [Formalism.AUTREP.InertDatum.loc, Units.val_mul, Units.val_mul]
    congr 2
  rw [mem_UJ_iff, hloc, ← Dv.Panti]
  exact cT_conj_form Dv.σw _ _ _ (by simp) hX'

end GlobalTheory.LocalUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add (f := _), GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_surj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  let sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
  let eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) :=
    Dv.e.symm.toRingHom
  have hcomm : ∀ a, sig (eS a) = eS (Dv.σw a) := by
    intro a
    apply Dv.e.injective
    have h := Dv.comm (eS a)
    simp only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢
    exact h
  let Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) _)
  let Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)
  let Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (y : Matrix (Fin n) (Fin n) _)
  have hPQ : Pm * Qm = 1 := by simp [Pm, Qm]
  have hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let X := Pm * Ym * Qm
  have hX : Formalism.UG.cT Dv.σw X * X = 1 := by
    have hP := Dv.Panti
    change Formalism.UG.cT Dv.σw Pm * Pm = _ at hP
    calc Formalism.UG.cT Dv.σw X * X
        = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Ym * (Formalism.UG.cT Dv.σw Pm * Pm) * Ym) * Qm := by
          simp only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']
      _ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]
  have hX' : X * Formalism.UG.cT Dv.σw X = 1 := mul_eq_one_comm.mp hX
  let M := X.map eS
  have hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS := by
    ext i j
    simp [M, conjT, Formalism.UG.cT, hcomm]
  have hM : M * conjT sig M = 1 := by
    rw [hMc]
    change X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1
    rw [← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v
  let E : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1
  have hEv : compAt L v E = 1 := by
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hEw : ∀ u, u ≠ v → compAt L u E = 0 := by
    intro u hu
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]
  let Z : Matrix (Fin n) (Fin n) (AL L) := M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))
  have hZv : Z.map (compAt L v) = M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]
  have hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) =
      conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L)))
        (Z.map (compAt L u)) := by
    intro u
    ext i j
    simp [conjT, GlobalTheory.InertSurj.compAt_conjAL]
  have hZZ : Z * conjT (conjAL L) Z = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1 := by
      rw [Matrix.map_mul, hZconj]
      rcases eq_or_ne u v with rfl | hu
      · rw [hZv]; exact hM
      · rw [hZw u hu, conjT_one, Matrix.one_mul]
    have h1 := congrFun (congrFun key i) j
    have h2 := congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZZ' : conjT (conjAL L) Z * Z = 1 := mul_eq_one_comm.mp hZZ
  let g : GL (Fin n) (AL L) := ⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := hZZ
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hZw u (by simpa using hu)
  · have hb : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) =
        Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      change (Z.map (compAt L v)).map _ = X
      rw [hZv]
      ext i j
      simp [M, eS]
    unfold InertDatum.loc
    rw [hb]
    group

end GlobalTheory.InertSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KUTransfer

theorem ku_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  intro L _ _ _ n w σ b hb p hp x
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  have hK : ∀ g : GL (Fin n) (w.adicCompletion L), g ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      g ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := by
    intro g
    show g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L w) ↔ _
    rw [hO]; rfl
  have h1 : p x ∈ Formalism.UG.KU σ n ↔ (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [hK]
    show (p x).val ∈ Formalism.UG.intPts (Formalism.UG.intL _).subtype (Formalism.UG.GU σ n) ↔ _
    exact ⟨fun h => h.2, fun h => ⟨(p x).2, h⟩⟩
  rw [h1, hp]
  have hbi : b⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hb
  constructor
  · intro h
    have := (GlobalTheory.LFun.KGL w (n := n)).mul_mem (( GlobalTheory.LFun.KGL w (n := n)).mul_mem hb h) hbi
    simpa [mul_assoc] using this
  · intro h
    exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem hbi h) hb

end GlobalTheory.KUTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishing
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacMinCuspGL

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

theorem isCuspidal_jac₂_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) →
    IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  intro k _ _ _ _ a b n h V _ _ π hπ hmin
  set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef
  refine (isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)),
    fun r t h' hr ht => ?_⟩
  have hcd : a + r + t = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)

  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K' := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg1 : g.1 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg2 : g.2 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.2 = 1 := det_eq_one_of_mem_unipRad k hg2
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    have hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v) := by
      rw [hu_eq, map_mul, Module.End.mul_apply]
      show jac₂ (stdSum h) π (1, g.2) _ = _
      rw [hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]
      refine (Submodule.Quotient.eq Kab).2 ?_
      rw [← map_sub]
      refine twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_
      have := (Submodule.Quotient.eq Kab).1 (hN n' hn' v)
      rw [← neg_sub]
      exact Kab.neg_mem this
    rw [← hJu]
    exact Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Kab x
  have hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    simpa [Submodule.mkQ_apply] using hC u u.2 w
  exact hle (hJ ▸ Submodule.mem_top)

end GlobalTheory.JacMinCuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem isSubquotient_jac_refine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (GlobalTheory.SmGL.jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (GlobalTheory.SmGL.jac E π) := by
  intro k _ _ _ _ n s d e V _ _ π hπ X _ _ ρ _ hsub t d' e' Y _ _ ρ' hρ'
  refine ⟨refinePlace e e', ?_⟩
  refine isSubquotient_of_comp (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _) ?_
  obtain ⟨φR⟩ := _root_.GlobalTheory.JacStages.piTensor_flatHom_equiv s t (fun a b => GL (Fin (d' a b)) k) Y ρ'
  obtain ⟨φT⟩ := _root_.GlobalTheory.JacStages.relJacD_piTensor_equiv k s d t d' e' X ρ
  obtain ⟨φS⟩ := _root_.GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s n d e t d' e' V π
  have h1 : IsSubquotient (piTensor fun a => piTensor (ρ' a)) (piTensor fun a => GlobalTheory.SmGL.jac (e' a) (ρ a)) :=
    GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ hρ'
  have h3 := _root_.GlobalTheory.JacStagesExact.isSubquotient_relJacD k s d t d' e' _ _ (piTensor ρ) (GlobalTheory.SmGL.jac e π) (isSmooth_jac e hπ) hsub
  exact (isSubquotient_of_equiv φR).trans (h1.trans ((isSubquotient_of_equiv φT.symm).trans
    (h3.trans (isSubquotient_of_equiv φS.symm))))

end GlobalTheory.JacStages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompareApply

theorem lift_localArtinMap_apply : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι σ τ hτ z hz
  have H := GlobalTheory.ArtinCompare.restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ τ hτ
  set M := maximalAbelianExtension (w.adicCompletion E) (Kbar w)
  set g := localArtinMap (w.adicCompletion E) (Kbar w) (a σ)
  have e : AlgEquiv.restrictNormalHom M τ (g ⟨z, hz⟩) = ⟨z, hz⟩ := by
    rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have e2 := congrArg (fun y : M => (y : Kbar w)) e
  simp only [AlgEquiv.restrictNormalHom_apply] at e2
  exact e2

end GlobalTheory.ArtinCompareApply
end

