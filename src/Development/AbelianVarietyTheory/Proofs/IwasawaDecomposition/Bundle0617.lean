module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagFibre

theorem sp_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (a : B →+* C') (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem carries_every : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ i K _ _ χ x hx g g' p hp hc
  obtain ⟨L, _, _, ι, s, hs, hV⟩ := _root_.GlobalTheory.genval K
  obtain ⟨gL, hgL⟩ := _root_.GlobalTheory.GenFrame.exists_generic_frame E H Dw l Xo c O β Z K χ (x ≫ genι Z) g g' L ι s hs ((spMap ι ≫ x) ≫ genι Z)
    (Category.assoc _ _ _)
  have hxL : (spMap ι ≫ x) ≫ genStr Z = spMap (ι.comp χ) := by
    rw [Category.assoc, hx, sp_comp]
  obtain ⟨⟨j, pL⟩, ⟨hpL, hcL⟩, -⟩ := Φ.lifts L (ι.comp χ) (spMap ι ≫ x) hxL gL
  have spec : ∀ (a : K) (b : EigFrame Z χ (x ≫ genι Z)), (∀ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K)
      (sV : V), (algebraMap V L).comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V →
      algebraMap V L sV = s → r sV = a → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x ≫ genι Z))
        (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ),
        gV.Tri (algebraMap V L) gL tL ∧ gV.Tri r b tk) →
      ∃ p' : Sp K ⟶ (Φ.C j).Y.X, p' ≫ (Φ.C j).π = x ∧ (Φ.C j).Carries p' b := by
    intro a b hb
    obtain ⟨V, ιV, r, sV, h1, h2, h3, h4, h5⟩ := hV a
    obtain ⟨gV, tL, tk, hTL, hTk⟩ := hb V ιV r sV h1 h2 h3 h4 h5
    have hpL' : pL ≫ (Φ.C j).π = spMap (algebraMap V L) ≫ (spMap ιV ≫ x) := by
      rw [hpL, ← Category.assoc, ← sp_comp, h1]
    obtain ⟨q, hq1, hq2⟩ := _root_.GlobalTheory.FlagCptLift.exists_lift E H Dw l Xo c O β Z F e (Φ.C j) V L (spMap ιV ≫ x) pL hpL'
    have hc' : (Φ.C j).Carries (spMap (algebraMap V L) ≫ q) gL := by rw [hq2]; exact hcL
    have hxV : spMap ιV ≫ x ≫ genι Z = q ≫ (Φ.C j).π ≫ genι Z := by
      rw [← Category.assoc q, hq1, Category.assoc]
    refine ⟨spMap r ≫ q, ?_, _root_.GlobalTheory.CarrySpec.carries_spec E H Dw l Xo c O β Z F e (Φ.C j) V L (algebraMap V L)
      (IsFractionRing.injective V L) K r h3 q (ιV.comp χ) _ hxV gV (ι.comp χ) _ gL tL hTL hc' χ _ b tk hTk⟩
    rw [Category.assoc, hq1, ← Category.assoc, ← sp_comp, h2, sp_id, Category.id_comp]
  obtain ⟨p₀, hp₀, hc₀⟩ := spec 0 g fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).1 h5
  obtain ⟨p₁, hp₁, hc₁⟩ := spec 1 g' fun V ιV r sV h1 h2 h3 h4 h5 => (hgL V _ ιV r sV h1 h2 h3 h4).2 h5
  obtain ⟨_, -, hu⟩ := Φ.lifts K χ x hx g
  have hij : i = j := congrArg Sigma.fst ((hu ⟨i, p⟩ ⟨hp, hc⟩).trans (hu ⟨j, p₀⟩ ⟨hp₀, hc₀⟩).symm)
  subst hij
  exact ⟨p₁, hp₁, hc₁⟩

end GlobalTheory.FlagFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem galoisRepsCusp_of_galEx {D : D7} (h : GalEx D) : GlobalTheory.BlockComplement.GaloisRepsCusp D :=
  fun i a ha π hc hr => h (D.nd.l i) (D.naut.iotaQC i) a ha π hc hr


end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))


set_option maxHeartbeats 2000000 in
theorem rrT_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (y₀ : Hd z₀.R.toRealDat) (bb : Bool) (E : Hs)
    (jE : E.T →ₗ[ℂ] (y₀.C z₀.F.lv2).Amb 0) (n : ℕ) (c : Module.Basis (Fin n) ℂ E.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT z₀.F y₀ bb jE n c Xo) :
    ∀ (y : Hd z.R.toRealDat) (jE' : E.T →ₗ[ℂ] (y.C z.F.lv2).Amb 0), HEq jE' jE → RrT z.F y bb jE' n c Xo := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  intro y jE' hj
  exact (by with_unfolding_all exact (((@rr_eta_tr B C a b _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).2 y₀ ((y)) bb E jE ((jE')) n c ((Xo)) ((hj)) h) : _))

end Copy


set_option maxHeartbeats 1000000 in
theorem coords {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : RationalReadingWithoutCongruence R F X0 Y) (y : Hd R.toRealDat)
    (heq_eigen_embedding_zero : D.what₂.EE0 →ₗ[ℂ] (y.C F.lv2).Amb 0) (hinj : Function.Injective heq_eigen_embedding_zero) (n : ℕ) (c : Module.Basis (Fin n) ℂ D.what₂.EE0)
    (Xo : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ) (h : RrT F y false (E := ⟨D.what₂.EE0⟩) heq_eigen_embedding_zero n c Xo)
    (hz : ∀ v, HEq (Y.Iz.jE v).1 (heq_eigen_embedding_zero v)) :
    ∃ ε : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n → D.what₂.LL), (∀ x, X0.s.jEE x = ∑ i, D.what₂.embLL (ε x i) • c i) ∧
      ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n)) Xo v (ε x) (ε x') := by
  obtain ⟨rfl, a0, b0⟩ := h
  refine ⟨Z.eRR0.symm, fun x => hinj ?_, fun v hv x x' => ?_⟩
  · have h := Z.jEE0 (Z.eRR0.symm x)
    rw [Z.eRR0.apply_symm_apply] at h
    exact (eq_of_heq (hz _)).symm.trans (h.trans (a0 (Z.eRR0.symm x)).symm)
  · have h := Z.met0 v hv (Z.eRR0.symm x) (Z.eRR0.symm x')
    rw [Z.eRR0.apply_symm_apply, Z.eRR0.apply_symm_apply] at h
    exact h.trans (GoodSideLattices.majAt_cast rfl _ Xo v (b0 v).1 _ _).symm

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}


set_option maxHeartbeats 1000000 in
theorem RRset_two {o o' : q.Over} (s : Side0 o) (s' : Side0 o') (μ : (w.D o.Z).what₂.Tup) :
    s.p0.s.RRset μ = (s'.p0.s.RRset μ) := by
  have h : ∀ k, s.p0.s.downTo μ k = (by with_unfolding_all exact ((s'.p0.s.downTo ((μ)) k) : _)) := by
    intro k
    induction k with
    | zero => exact (by with_unfolding_all exact ((Eq.refl (s.p0.s.downTo μ 0)) :))
    | succ k ih => exact (by with_unfolding_all exact ((congrArg (fun φ : type_of% (s.p0.s.downTo μ k) => φ.comp (s.p0.s.io μ k)) ih) :))
  have hi := congrArg (fun φ : type_of% (s.p0.s.downTo μ (w.D o.Z).R.m) =>
    (s.p0.s.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (s.p0.s.multTop μ).symm.toLinearEquiv.toLinearMap) (h (w.D o.Z).R.m)
  exact (by with_unfolding_all exact ((congrArg (fun φ : s.p0.s.Amb μ →ₗ[ℂ] (w.D o.Z).what₂.EE0 =>
    φ '' ((fun x => (s.p0.s.V0 μ ⊓ (s.p0.s.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
      ((s.p0.s.Mtilde μ).carrier ∩ (s.p0.s.V0 μ : Set (s.p0.s.Amb μ))))) hi) :))


set_option maxHeartbeats 1000000 in
theorem rrT_moved {o : q.Over} (m : Moved o) (hc : m.Copy) (hco : m.Coh) (b : Bool) {n c Xo}
    (h : RrT z₀.F q.y b (q.t.ch b).jE n c Xo) : RrT m.z.F m.y b (m.t.ch b).jE n c Xo :=
  rrT_copy (B := B) (C := w.C) (a := Z₀) o.Z z₀ m.z m.Xg m.tr ((by with_unfolding_all exact (hc.core :))) ((by with_unfolding_all exact (hc.R :))) q.y b _ _ n c Xo h m.y _ (hco.jE b)

theorem lat_tr {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {n : ℕ} (c : Module.Basis (Fin n) ℂ V) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) {S S' : ι → Set V} (hS : S = S') {RR RR' : HLat K} (hR : RR' = RR)
    {j : RR.V →ₛₗ[e] V} {j' : RR'.V →ₛₗ[e] V} (hj : HEq j' j)
    (h : ∃ ε : RR.V ≃ₗ[K] (Fin n → K), (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u}) :
    ∃ ε : RR'.V ≃ₗ[K] (Fin n → K), (∀ x, j' x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR'.b RR'.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR'.V, x ∈ RR'.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j' z ∈ S' u} := by
  subst hS hR
  cases hj
  exact h


set_option maxHeartbeats 2000000 in
theorem good_copy {K : Ctx} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)) (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hc : m.Copy)
    (hco : m.Coh) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) (hR : s.RR = x.s.RR) (hj : HEq s.jEE x.s.jEE) : GoodSideLattices.Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st P.Z₀).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T P.Wt))
    (famR (w.st P.Z₀) w.I P.hX (usedOf w.I T P.Wt) P.z.Xg P.z.tr) P.z.core.Q.c.F P.z.R P.z.F P.z.cG P.z.pins P.intersectionNumber_baseChange P.q.y false
    (P.q.p.ch false).EE (P.q.t.ch false).jE (P.q.t.ch false).jE_inj (P.q.t.ch false).jE_range
  have h0 := rrT_moved x.m x.copy x.coh false h
  have h1 := rrT_moved m hc hco false h
  have h2 := coords x.r.Z x.m.y ((by with_unfolding_all exact ((x.m.t.ch false).jE :))) ((by with_unfolding_all exact ((x.m.t.ch false).jE_inj :))) n ((by with_unfolding_all exact (c :))) ((by with_unfolding_all exact (Xo :))) ((by with_unfolding_all exact (h0 :))) ((by with_unfolding_all exact (x.pin.heq_eigen_embedding_zero :)))
  obtain ⟨ε, h2, h3⟩ := h2
  have h4 : (fun u : B.places.Pl => ((by with_unfolding_all exact ((x.s.p0.s.RRset ((w.D x.o.Z).what₂.muAt u)) :)) : Set (P.q.p.ch false).EE.T)) =
      fun u => (by with_unfolding_all exact ((s.p0.s.RRset ((w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).what₂.muAt u)) :)) :=
    funext fun u => (by with_unfolding_all exact ((RRset_two x.s s ((w.D x.o.Z).what₂.muAt u)) :))
  have h5 := lat_tr (K := B.LL) B.embLL c Xo ((by with_unfolding_all exact ((fun u : B.places.Pl => (w.D x.o.Z).plEq u) :))) h4 hR hj
    ⟨(by with_unfolding_all exact (ε :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (x.r.Z.rr0 :))⟩
  obtain ⟨ε', k1, k2, k3⟩ := h5
  exact ⟨n, c, Xo, ε', h1, k1, k2, (by with_unfolding_all exact (k3 :))⟩

end GlobalTheory.Mem.R3.Rw.CopyRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr


set_option maxHeartbeats 4000000 in
theorem goodO_setDiv : ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), GoodO D nch xd → GoodO (setDiv D N h) (nchTr N h nch) (xdTr N h xd) := by
  intro D nch xd N h hg
  obtain ⟨⟨⟨E, N0, S⟩, hE, hA, hC⟩, hsep⟩ := hg
  subst hE
  exact ⟨⟨⟨{ (twEOf xd) with }, N0, S⟩, rfl, hA, hC⟩, hsep⟩

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigISupEqTopOfSep
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.heckeEig_iSup_eq_top_of_sep {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Finite X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    ⨆ x, heckeEig T act x = ⊤ := by
  classical
  have := Fintype.ofFinite X
  have hs' : ∀ x y : X, ∃ f : T, x ≠ y → (f : X → O) x ≠ (f : X → O) y := by
    intro x y
    by_cases h : x = y
    · exact ⟨1, fun h' => (h' h).elim⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y h
      exact ⟨⟨f, hf⟩, fun _ => hne⟩
  choose s hs using hs'
  let E : X → T := fun x => ∏ y ∈ Finset.univ.erase x, (s x y - algebraMap O T ((s x y : X → O) y))
  have hE : ∀ x z, ((E x : T) : X → O) z = ∏ y ∈ Finset.univ.erase x, ((s x y : X → O) z - (s x y : X → O) y) := by
    intro x z
    simp [E, Subalgebra.coe_prod, Finset.prod_apply]
  let d : X → O := fun x => ((E x : T) : X → O) x
  have hd : ∀ x, d x ≠ 0 := by
    intro x
    simp only [d, hE]
    exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (hs x y (Ne.symm (Finset.ne_of_mem_erase hy)))
  have hE0 : ∀ x z, z ≠ x → ((E x : T) : X → O) z = 0 := by
    intro x z hz
    rw [hE]
    exact Finset.prod_eq_zero (i := z) (Finset.mem_erase.mpr ⟨hz, Finset.mem_univ _⟩) (sub_self _)
  have hmul : ∀ (g : T) x, g * E x = ((g : X → O) x) • E x := by
    intro g x
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst hz; simp
    · simp [hE0 x z hz]
  let F : X → O := fun x => ∏ x' ∈ Finset.univ.erase x, d x'
  let c : O := ∏ x, d x
  have hsum : ∑ x, F x • E x = algebraMap O T c := by
    apply Subtype.ext
    funext z
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z]
    · simp only [F, c]
      show (∏ x' ∈ Finset.univ.erase z, d x') * d z = _
      rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ z)]
      simp
    · intro x _ hx
      rw [hE0 x z (Ne.symm hx), mul_zero]
    · intro h; exact (h (Finset.mem_univ z)).elim
  let K := FractionRing O
  let ψ : T →ₐ[O] Module.End K (TensorProduct O K M) := (Module.End.baseChangeHom O K M).comp act
  have hψ : ∀ f, ψ f = (act f).baseChange K := fun f => rfl
  have hmem : ∀ x (m : TensorProduct O K M), ψ (E x) m ∈ heckeEig T act x := by
    intro x m
    simp only [heckeEig]
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [Module.End.mem_eigenspace_iff, ← hψ]
    rw [show ψ f (ψ (E x) m) = (ψ f * ψ (E x)) m from rfl, ← map_mul, hmul, map_smul,
      LinearMap.smul_apply, algebraMap_smul]
  have hc : algebraMap O K c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hd x
  refine eq_top_iff.mpr fun m _ => ?_
  have hcm : algebraMap O K c • m = ∑ x, F x • ψ (E x) m := by
    rw [algebraMap_smul]
    have := congrArg (fun f => ψ f m) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, AlgHom.commutes] at this
    rw [LinearMap.sum_apply] at this
    simp only [LinearMap.smul_apply] at this
    rw [this, Module.algebraMap_end_apply]
  have : m = (algebraMap O K c)⁻¹ • (algebraMap O K c • m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, hcm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem x (hmem x m))

theorem eigSpan_of_record (D : D7) : D.nd.EigSpan :=
  fun i => GlobalTheory.heckeEig_iSup_eq_top_of_sep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGaloisStageFitsOfSameCentreActions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SwapN

open GlobalTheory.Mem.Top.TypesTrue

theorem heq_apply_cast {X : Type*} {P P' : Fin 2 → Type} (h : P = P') {a : ∀ k, P k → X} {a' : ∀ k, P' k → X}
    (ha : HEq a a') (k : Fin 2) (v : P k) : a' k (cast (congrFun h k) v) = a k v := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem cen_transport {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {c : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    {c' : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i z = c' i z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem cen_transport₂ {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι κ : Type*} {E : ι → κ → Type*}
    [∀ i j, AddCommGroup (E i j)] [∀ i j, Module ℂ (E i j)]
    {c : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    {c' : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (j : κ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i j z = c' i j z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem mem_center_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

end GlobalTheory.Mem.R3.Rw.SwapN

namespace GlobalTheory.Mem.R3.Rw.SwapN

theorem fits_swap : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  intro K B f T w P x N hG hP hw hA hM
  have hG' : GrpTrue x.o.N f := x.fits.grp
  obtain ⟨⟨plg, hplg⟩, hidem, hcen⟩ := x.fits.grpAt
  let e := grpEquiv N.naut x.o.N.naut
  have hco : ∀ g, x.o.N.ntypes.e0.coeff (e g) = N.ntypes.e0.coeff g := GrpTrue.typeIdempotent_coeff_across_layers hG hG'
  let φ := MonoidAlgebra.domCongr ℂ ℂ e
  have hφ : ∀ (a : MonoidAlgebra ℂ (G0g N.nd)) g, (φ a).coeff (e g) = a.coeff g := by
    intro a g
    simp [φ]
  have he0 : N.ntypes.e0 = φ.symm x.o.N.ntypes.e0 := by
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    show _ = (MonoidAlgebra.domCongr ℂ ℂ e.symm x.o.N.ntypes.e0).coeff g
    rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, hco]
  have hpe : ∀ k v, plEquiv N.naut x.o.N.naut k v = cast (congrFun hP k) v := by
    intro k v
    show (plF x.o.N.naut k).symm (plF N.naut k v) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [plF_apply, plF_apply, heq_apply_cast hP hw k v]
  have he : ∀ (g : G0g N.nd) k v, e g ⟨k, cast (congrFun hP k) v⟩ = g ⟨k, v⟩ := by
    intro g k v
    rw [grpEquiv_apply, ← hpe, Equiv.symm_apply_apply]
  refine ⟨⟨⟨(Equiv.sigmaCongrRight fun k => plEquiv N.naut x.o.N.naut k).trans plg, fun kv => ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hplg ⟨kv.1, plEquiv N.naut x.o.N.naut kv.1 kv.2⟩
    refine ⟨?_, h2⟩
    exact h1.trans (TypesTrue.plGw_plEquiv hG hG' kv.1 kv.2)
  · show IsIdempotentElem N.ntypes.e0
    rw [he0]
    exact hidem.map φ.symm
  · show N.ntypes.e0 ∈ _
    rw [he0]
    exact mem_center_map φ.symm hcen
  · rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    have hstd : StdIso (w.st x.o.Z) w.px (eR.trans e) := by
      refine ⟨(Equiv.sigmaCongrRight fun k => (plEquiv N.naut x.o.N.naut k).symm).trans plg1,
        fun kv => iso1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
      · refine (hpl1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩).trans ?_
        have := TypesTrue.plGw_plEquiv hG hG' kv.1 ((plEquiv N.naut x.o.N.naut kv.1).symm kv.2)
        exact ((congrArg (x.o.N.naut.plGw kv.1) (Equiv.apply_symm_apply (plEquiv N.naut x.o.N.naut kv.1) kv.2)).symm.trans
          this).symm
      · exact hact1 g _
    have hc := x.fits.cen _ hstd
    have hz1 : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))), φ (z : MonoidAlgebra ℂ (G0g N.nd)) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g x.o.N.nd)) := fun z => mem_center_map φ z.2
    refine ⟨fun μ z z' hz xx => ?_, fun μ j z z' hz xx => ?_⟩
    · have h1 := hc.amb μ ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport hP hA e he μ z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1
    · have h1 := hc.mt μ j ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport₂ hP hM e he μ j z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1

end GlobalTheory.Mem.R3.Rw.SwapN
end
end

