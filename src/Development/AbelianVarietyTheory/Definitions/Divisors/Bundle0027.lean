module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section Translates

variable {S : Scheme.{0}} (P : PolAV S)

def IsPolAVSectionInverseImage (T : Over S) (s : P.L.Sec) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U i),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f i)

def Tr (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {T : Over S} (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T))
    (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T) (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)),
    α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ t

def ThJetT (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {B : Type} [CommRing B] (s : Sp B ⟶ S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk s))) {I : Type} (pt : I → (Over.mk s ⟶ P.A)) {g : ℕ}
    (y : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s ⊗ P.A).left)) (ϑ : I → B) (J : I → Fin g → B) : Prop :=
  ∃ (U : I → ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)) (t : I → LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)))
    (i₀ : P.L.ι) (c : Fin g → B),
    (∀ i, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr P ρ m th (U i) (t i)) ∧
    ⊤ ≤ (s ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
    ∀ i j, valR (y j) ((LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)).U fun _ => i₀) ((t i).f fun _ => i₀) =
      TrivSqZeroExt.inl (valR s ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ (m ^ 2)) *
        (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i))

end Translates

def epsLift {R : Type} [CommRing R] {A : Over (Sp R)} (v : epsR R ⟶ A) :
    Sp (DualNumber R) ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk (epsR R).hom (by simp) : epsR R ⟶ baseOver (Sp R)) v).left

def ThJet {R : Type} [CommRing R] (x : KeyIn R) {g : ℕ} (hg : x.P.g = g) (m : ℕ) {I : Type}
    (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (ϑ : I → R) (J : I → Fin g → R) : Prop :=
  ∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧
    ThJetT x.P x.rig m (𝟙 (Sp R)) th pt (fun j => epsLift (x.v (j.cast hg.symm))) ϑ J

def Rule4 (κ : Rule) : Prop := Homog (fun _ => 1) κ ∧ Funct κ ∧ ThetaOne κ ∧ FamUnit κ

def KapF (κ : Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1

def Deform (κ : Rule) {C : Type} [NormedField C] [CharZero C] (e : C →+* ℂ) (x : KeyIn C) {g : ℕ} (hg : x.P.g = g) (m : ℕ)
    (ζ : Cˣ) (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) : Prop :=
  ∃ (Θ : (Fin (2 * g) → ZMod (m ^ 2)) → PowerSeries C) (Γ : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → PowerSeries C) (π : C) (b : ℝ),
    ‖π‖ < 1 ∧ (∀ a n, ‖PowerSeries.coeff n (Θ a)‖ ≤ b ∧ ∀ j, ‖PowerSeries.coeff n (Γ a j)‖ ≤ b) ∧
    ThJet x hg m (levelPoint lev hg) (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n)
      (fun a j => ∑' n, PowerSeries.coeff n (Γ a j) * π ^ n) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a, (Summable fun n => ‖e (PowerSeries.coeff n (Θ a)) * u ^ n‖) ∧
        ∀ j, Summable fun n => ‖e (PowerSeries.coeff n (Γ a j)) * u ^ n‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n)
          (fun a j => ∑' n, e (PowerSeries.coeff n (Γ a j)) * u ^ n) ∧ (κ ℂ x₀ : ℂ) = e k

def Transfer (κ : Rule) : Prop :=
  ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀,
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      (e : C →+* ℂ) (x : KeyIn C) (hg : x.P.g = g) (ζ : Cˣ) (lev : Out.Level x.P ((n ^ j) ^ 2) (unitOn ζ)) (k : C),
      Deform κ e x hg (n ^ j) ζ lev k → (κ C x : C) = k

section Jets

abbrev redE (F : Type) [CommRing F] : Sp F ⟶ Sp (DualNumber F) := spMap (TrivSqZeroExt.fstHom F F F).toRingHom

variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vE (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (t.s fun k => J (redE F ≫ r ≫ φ k)).val

def sE (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (s.f fun k => J (redE F ≫ r ≫ φ k))

end Jets

section GtJets

variable {R : Type} [CommRing R] [IsDomain R]

abbrev TE (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : Over (Sp R) :=
  Over.mk (spMap (algebraMap F (DualNumber F)) ≫ (TF (R := R) F).hom)

def dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm, add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def jc (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (gm : GtPt D (TE R F)) (α : N.X) : DualNumber F :=
  sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ν.J *
    vE (gm.s (ν.eX α)) (𝟙 _) ν.J

def Adapted (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) {r g : ℕ} (bX : Module.Basis (Fin r) ℤ N.X)
    (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)) : Prop :=
  IsLieBasis vB ∧ (∀ j, ∃ o : GtPtF D F, o.IsZero ∧ GtPt.IsPullF F (redE F) (gm j) o) ∧
  (∀ i, (gm (σ.symm (Sum.inl i))).b.left =
    spMap (dualMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) ∧
  ∀ l, (gm (σ.symm (Sum.inr l))).b = DegPre.zeroT D (TE R F) ∧
    ∀ χ, vE ((gm (σ.symm (Sum.inr l))).s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : F)

def BKey (κ : Rule) [CharZero F] (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) : Prop :=
  (D.P.g = 0 → N.th 1 ^ 8 * k = 1) ∧
  ∀ (hg : 1 ≤ D.P.g) (hr : D.rig.IsGen) (th : D.P.L.Sec) (hth) (hv : IsLieBasis vB) (x : KeyIn F),
    (∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
      ν.th.f (fun _ => i) = resG _ h (th.f i)) →
    KeyPB x ⟨D.P, hg, D.rig, hr, th, hth, vB, hv⟩ ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) →
    (κ F x : F) = k

end GtJets

def QLevel {O : Type} [CommRing O] (N : NumD O) (g k : ℕ) (ζ : Oˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k) : Prop :=
  IsPrimitiveRoot ζ k ∧ (∀ a b, N.QEq (q a * q b) (q (a + b))) ∧ (∀ a b, N.QEq (q a) (q b) → a = b) ∧
  (∀ p, ∃ a, N.QEq (q a) p) ∧ ∀ i j, N.wp (q (Pi.single i 1)) (q (Pi.single j 1)) = ζ ^ stdSymp g i j

def IsEvFam {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (f : N.X → N.A → O) : Prop :=
  (∀ (h : N.Gt) (χ : N.X), f (p.1.1.toAdd + m • χ) h.b * h.s (p.1.1.toAdd + m • χ) = N.evT m p h χ) ∧
  ∀ α, (∀ χ, α ≠ p.1.1.toAdd + m • χ) → ∀ x, f α x = 0

def Arch (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g r m k : ℕ), 1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D ℂ (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R ℂ)), Adapted ν vB bX σ gm → ∀ k₀ : ℂ, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖(jc ν (s a) (gm j) α).fst * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖(jc ν (s a) (gm j) α).snd * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn ζ)) (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = k₀

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f

end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

end GlobalTheory.LKLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def htInf (y : GL (Fin a) (Cinf E)) : ℝ :=
  ∏ w : InfinitePlace E, htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y)

def kerInf {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

def rspan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    (∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S)}

theorem mem_rspan {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ rspan π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem rt_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem kerInf_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X ν k γ hk

theorem rspan_le {π : CuspSub E a} {S : Submodule ℂ (GA E a → ℂ)} (h₁ : ∀ φ ∈ π.V, φ.1 ∈ S)
    (h₂ : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S)
    (h₃ : ∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S) : rspan π ≤ S :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem one_le_htInf (y : GL (Fin a) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htInf_pos (y : GL (Fin a) (Cinf E)) : 0 < htInf y := lt_of_lt_of_le one_pos (one_le_htInf y)

theorem htGL_le_htInf (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf (y : GL (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf y w))

theorem height_le_htInf (y : GL (Fin a) (Cinf E)) : height y ≤ 3 * htInf y := by
  have h0 := (htInf_pos y).le
  have h1 : ‖toL y.val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).1
  have h2 : ‖toL (y⁻¹).val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).2
  unfold height
  linarith [one_le_htInf y]

theorem IsRapidInf.of_htInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : Measurable k) (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i j)
    (hm : ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htInf (γ x) ^ N) ν) : IsRapidInf ν k γ := by
  refine ⟨hk, Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j, fun N => ?_⟩
  refine ((hm N).const_mul (3 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hk.norm.mul ?_).aestronglyMeasurable
    have hm' : Measurable fun x => toL (γ x).val :=
      Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j
    have hi : Measurable fun x => toL ((γ x)⁻¹).val := by
      refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
      set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
        Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      have e : (fun x => toL ((γ x)⁻¹).val i j w) =
          fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
        funext x
        rw [← map_inv]; rfl
      rw [e]
      exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)
        ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
          ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem i j)
        fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
    unfold height
    exact ((measurable_const.add hm'.norm).add hi.norm).pow_const N
  · have h0 : 0 ≤ height (γ x) := by unfold height; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖k x‖ * height (γ x) ^ N ≤ ‖k x‖ * (3 * htInf (γ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf _) N) (norm_nonneg _)
      _ = 3 ^ N * (‖k x‖ * htInf (γ x) ^ N) := by rw [mul_pow]; ring

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have e : chart φ g = (invSet E a).piecewise (chart φ g) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact dif_neg hx
  rw [e]
  exact (hφ g).continuousOn.measurable_piecewise continuousOn_const isOpen_invSet.measurableSet

theorem measurable_comp_infGL {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => φ (g * infGL E a (γ x)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun x => φ (g * infGL E a (γ x))) = fun x => chart φ g (toL (γ x).val) :=
    funext fun x => (chart_val φ g (γ x)).symm
  rw [e]
  exact (measurable_chart hφ g).comp h

theorem IsRapidInf.integrable {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a}
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) :
    Integrable (fun x => k x * φ (g * infGL E a (γ x))) ν := by
  obtain ⟨C, N, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by unfold height; positivity) N
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hk.2.2 N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hk.1.mul (measurable_comp_infGL hφ g hk.2.1)).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖k x‖ * ‖φ (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_ne_bot (π : CuspSub E a) : rspan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  intro hb
  have h := mem_rspan hφ
  rw [hb, Submodule.mem_bot] at h
  exact h0 (Subtype.ext h)

theorem rspan_le_leftInv (π : CuspSub E a) : rspan π ≤ SpanModel.leftInv E a := by
  refine rspan_le (fun φ hφ => (π.cusp φ hφ).1.left) (fun F hF h γ g => ?_) fun F hF X _ ν _ k γ _ γ' g => ?_
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change kerInf ν k γ F (ratGL E a γ' * g) = kerInf ν k γ F g
    simp only [kerInf, mul_assoc]
    congr 1
    funext x
    rw [hF γ']

theorem rspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  rspan_le_leftInv π hF γ g

theorem rspan_eq_mspanR (π : CuspSub E a) : rspan π = mspanR π := by
  refine le_antisymm (rspan_le ?_ ?_ ?_) ?_
  · exact fun φ hφ => Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ
  · exact fun F hF h => Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h
  · exact fun F hF X _ ν _ k γ hk => Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk
  · refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF X _ ν _ k γ hk => ?_⟩
    exact kerInf_mem_rspan hF ν hk


open Classical in
def plS (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun z := Pi.single w z
  map_mul' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]
  map_zero' := by ext w'; simp [Pi.single_apply]
  map_add' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]

def plGL (w : InfinitePlace E) : GL (Fin a) ℂ →* GL (Fin a) (Cinf E) := cornerGL a (plS w)



theorem isRapidInf_dirac (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem kerInf_dirac (y : GL (Fin a) (Cinf E)) (F : GA E a → ℂ) (g : GA E a) :
    kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F g = F (g * infGL E a y) := by
  simp [kerInf]

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE
section
noncomputable section
namespace GlobalTheory.KS
namespace Model
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

theorem act_zero {A : Over S} [GrpObj A] (act : OActN O A) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have : act.act 0 * act.act 0 = act.act 0 * 1 := h.symm.trans (_root_.mul_one _).symm
  exact mul_left_cancel this

variable (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E]

section Gal
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

end Gal

theorem powMap_pr {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) : powMap f φ h m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_over {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) : powMap f φ h m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

end Model
end GlobalTheory.KS
end
end

