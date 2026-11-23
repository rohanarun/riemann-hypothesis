module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionEqColumnsTestFunction
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopPhi

theorem topPhi : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y
  have hm : R.m = s + 2 := hA.steps
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) :=
    fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrdY E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  rw [hmat]
  exact hPhi.2 E1' E1 hE1' hE1 _

end GlobalTheory.TwBridge.TopPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRational
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

namespace GlobalTheory.DenseBox

theorem isOpen_box_set {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : Type) [Fintype A] (c : kˣ) : IsOpen ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
  have e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) =
      ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c := by
    ext y; simp [GlobalTheory.StepData.mem_box, cball]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)

theorem support_invariance_of_dense : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  intro k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y
  have hv : DenseRange (fun y : A → E => fun a => ι (y a)) := DenseRange.piMap (fun _ => hι)
  have hM : DenseRange (fun x : Matrix A B E => x.map ι) := by
    have : DenseRange (fun x : A → B → E => fun a b => ι (x a b)) :=
      DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
    exact this
  have hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y} := hf.isOpen_fiber _
  refine ⟨fun hne => ?_, fun z hz => ?_⟩
  ·
    let U : Set (Matrix A B k × (A → k)) :=
      {p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}
    have hU : IsOpen U := hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))
    have hxy : (x, y) ∈ U := ⟨rfl, by simp⟩
    obtain ⟨⟨x0, y0⟩, hp⟩ := (hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩
    obtain ⟨h1, h2⟩ := hp
    have hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0 := by
      simp only [Set.mem_setOf_eq, Prod.map] at h1; rw [h1]; exact hne
    have hy0 := hsupp x0 y0 hne'
    have h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹ := h2
    have := Submodule.sub_mem _ hy0 h2'
    simpa using this
  ·
    have hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)} := hf.isOpen_fiber _
    let V : Set (Matrix A B k × (A → k) × (A → k)) :=
      {q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩
        {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}
    have hV : IsOpen V := by
      refine (IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))
      · exact hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      · exact hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add
          (continuous_snd.comp continuous_snd)))
    have hxyz : (x, y, z) ∈ V := ⟨⟨rfl, rfl⟩, hz⟩
    obtain ⟨⟨x0, y0, z0⟩, hp⟩ := (hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3
    have e := hinv x0 y0 z0 h3
    have e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a)) := by
      funext a; simp
    rw [e'] at e
    rw [← h2, e, h1]

end GlobalTheory.DenseBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NrmStepZeroEq
section
noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointDeterminantDiamondOperatorInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpMemRange
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.KerDia.SharpPoly

theorem detShift_shW {N : ℕ} (lam : DomWeight N) (c : ℤ) (h : 0 < N) :
    (GlobalTheory.Mem.Col2.shW lam c).detShift = lam.detShift + c := by
  unfold DomWeight.detShift; rw [dite_eq_left h, dite_eq_left h]; rfl

theorem half_cast (R : Ranks) : ((((R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h : (R.t + 1) / 2 = a + 1 := by omega
  rw [h, ha]; push_cast; ring

theorem wtN_last {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    Examples₂.wtN P (R.N (i + 1) - 1) = -wG R (P.e ⟨i, hi⟩) (i + 1) := by
  have hN : R.N (i + 1) = R.k + i * (R.t + 1) + R.t + 1 := by unfold Ranks.N; ring
  have hq : Examples₂.blkN R (R.N (i + 1) - 1) = i := by
    unfold Examples₂.blkN
    rw [hN, show R.k + i * (R.t + 1) + R.t + 1 - 1 - R.k = R.t + (R.t + 1) * i by
      rw [Nat.mul_comm (R.t + 1) i]; omega]
    rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), Nat.zero_add]
  unfold Examples₂.wtN
  rw [dite_eq_right (by omega), dite_eq_left (by rw [hq]; exact hi)]
  simp only [hq]

theorem exp_nonneg {R : Ranks} {ι : Type} (hc : ι → HCParam R) (i : ℕ) (hi : i < R.m) (τ : ι) (s : ℤ)
    (hs : (s : ℚ) = sExp' R ((hc τ).e ⟨i, hi⟩) (i + 1)) : 0 ≤ (GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s := by
  have hN := R.N_pos i
  have h1 : ((GlobalTheory.Mem.Col2.lamT hc i τ).detShift : ℚ) = Examples₂.wtN (hc τ) (R.N i - 1) - (i : ℚ) * (((R.t : ℚ) + 1) / 2) := by
    unfold GlobalTheory.Mem.Col2.lamT
    rw [detShift_shW _ _ hN]
    unfold DomWeight.detShift
    rw [dite_eq_left hN]
    rw [Int.cast_add, Int.cast_neg, Int.cast_mul, half_cast, Examples₂.lamOf_eq _ i hi.le, Examples₂.wtQ_eq_wtN]
    push_cast
    ring
  have h2 := wtN_last (hc τ) i hi
  have hle : R.N i ≤ R.N (i + 1) := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hlt : R.N (i + 1) - 1 < R.N R.m := by
    have := Examples₂.N_mono (R := R) (j := i + 1) (by omega)
    have := R.N_pos (i + 1)
    omega
  have h3 := Examples₂.wtN_anti (hc τ) (show R.N i - 1 ≤ R.N (i + 1) - 1 by omega) hlt
  have h4 : (((GlobalTheory.Mem.Col2.lamT hc i τ).detShift + s : ℤ) : ℚ) ≥ 0 := by
    rw [Int.cast_add, h1, hs]
    rw [h2] at h3
    simp only [wG, sExp', Ranks.N] at h3 ⊢
    push_cast at h3 ⊢
    linarith
  exact_mod_cast h4

end GlobalTheory.KerDia.SharpPoly

namespace GlobalTheory.KerDia.SharpPoly

def detP {ι : Type} (n : ℕ) (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (Matrix.of fun a b => (MvPolynomial.X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

theorem eval_detP {ι : Type} {n : ℕ} (y : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) (detP n τ) = (y τ).det := by
  unfold detP
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

end GlobalTheory.KerDia.SharpPoly

theorem GlobalTheory.KerDia.sharp_mem_range : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ x ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i), (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) := by
  intro B X I l u a i hi x hx
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.mp hx
  set n : Tau B.R → ℤ := fun τ => (lamT (B.hcW u) i τ).detShift + (I.chain l u a).sSharp i τ with hn
  have hn0 : ∀ τ, 0 ≤ n τ := fun τ =>
    GlobalTheory.KerDia.SharpPoly.exp_nonneg (B.hcW u) i hi τ _ ((I.chain l u a).sSharp_eq i hi τ)
  refine ⟨P * ∏ τ, GlobalTheory.KerDia.SharpPoly.detP (B.R.N i) τ ^ (n τ).toNat, ?_⟩
  funext y
  have hd : ∀ τ, (y.1 τ).det ≠ 0 := fun τ => (y.2 τ).ne_zero
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, ColumnChain.sharp, mulFun, Pi.one_apply, Matrix.one_mul,
    zpow_zero, Finset.prod_const_one, one_mul, map_mul, map_prod, map_pow, GlobalTheory.KerDia.SharpPoly.eval_detP]
  have key : ∀ τ, deFr y τ ^ (I.chain l u a).sSharp i τ * (y.1 τ).det ^ shiftOf (lamT (B.hcW u) i) τ =
      (y.1 τ).det ^ (n τ).toNat := by
    intro τ
    rw [deFr, ← zpow_add₀ (hd τ), ← zpow_natCast, Int.toNat_of_nonneg (hn0 τ), hn, shiftOf, add_comm]
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (key τ).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCoset
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge


open Classical in
theorem twNext_rep_eq_of_sameDC {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i)
    (hinj : ∀ d d' : (twNext Ch sel mu cst st).β, (∀ P : rowSG Pr sel mu,
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) → d = d')
    (d d' : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu)
    (hs : SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) :
    (twNext Ch sel mu cst st).h d P = (twNext Ch sel mu cst st).h d' P := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · let P₀ : twQOff (Pr := Pr) sel mu := ⟨P.1, hP⟩
    let d'' : (twNext Ch sel mu cst st).β := ⟨Function.update d.1 P₀ (d'.1 P₀), d.2⟩
    have hall : ∀ Q : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) Q.1
        ((twNext Ch sel mu cst st).h d Q) ((twNext Ch sel mu cst st).h d'' Q) := by
      intro Q
      by_cases hQ : Q.1 ∈ twQOff (Pr := Pr) sel mu
      · by_cases e : (⟨Q.1, hQ⟩ : twQOff (Pr := Pr) sel mu) = P₀
        · have hQP1 : Q.1 = P.1 := congrArg (fun x : twQOff (Pr := Pr) sel mu => x.1) e
          have hQP : Q = P := Subtype.ext hQP1
          rw [hQP]
          have e1 : (twNext Ch sel mu cst st).h d'' P = (twNext Ch sel mu cst st).h d' P := by
            simp only [twNext, dif_pos hP, d'']
            rw [Function.update_self]
          rw [e1]; exact hs
        · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
            simp only [twNext, dif_pos hQ, d'']
            rw [Function.update_of_ne e]
          rw [e1]; exact twDC_refl _ _ _ _
      · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
          simp only [twNext, dif_neg hQ]
        rw [e1]; exact twDC_refl _ _ _ _
    have hdd := hinj d d'' hall
    have hc : d.1 P₀ = d'.1 P₀ := by
      have := congrArg (fun x : (twNext Ch sel mu cst st).β => x.1 P₀) hdd
      simpa [d''] using this
    simp only [twNext, dif_pos hP]
    exact congrArg (fun D => twRep Ch sel mu cst st P₀ D.1) hc
  · simp only [twNext, dif_neg hP]

theorem idxProd_twIdx : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  intro X Pr R Ch sel S₀ mu cst m2 G hok j b b' P hs
  rcases j with _ | i
  · rfl
  · by_cases hi : i + 1 ≤ m2
    · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) →
          ∀ b b' : st'.β, (∀ b b' : st'.β, (∀ P : rowSG Pr sel mu,
            SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P)) → b = b') →
          SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P) → st'.h b P = st'.h b' P := by
        rintro st' rfl b b' hinj hs
        exact twNext_rep_eq_of_sameDC Ch sel mu cst _ hinj b b' P hs
      exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_pos hi]) b b' (hok.inj i (by omega)) hs
    · by_cases hi2 : i + 1 = m2 + 1
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twUnitSt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b b'; rfl
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_pos hi2]) b b'
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twEmptySt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b; exact b.elim
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_neg hi2]) b b'

end GlobalTheory.TwBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem idxIsProd_of_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  intro X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex
  have hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr := Pr) cst.sharp i P.1 a a :=
    fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  rcases j with _ | i
  · obtain ⟨b, hb⟩ := hL.zero_uniq
    refine ⟨b, fun P => ?_, fun b' _ => hb b'⟩
    obtain ⟨b₀, hb₀⟩ := hex P
    rw [← hb₀, hL.zero_h, hL.zero_h]
  · have hi : i < s := by omega
    choose bP hbP using hex
    obtain ⟨b, hb⟩ := hL.surj i hi hh
      (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg)
      (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg)
      (fun P => by
        obtain ⟨al, hal⟩ := hL.nonvan i hi (bP P) P
        exact ⟨al, hbP P ▸ hal⟩)
    refine ⟨b, fun P => ?_, fun b' hb' => ?_⟩
    · have h1 := hb P
      rw [← hbP P] at h1 ⊢
      exact hP (i + 1) b (bP P) P h1
    · refine hL.inj i hi b' b (fun P => ?_)
      have e : L.h (i + 1) b' P = L.h (i + 1) b P := by
        have h1 := hb P
        rw [hb' P, ← hbP P] at *
        exact (hP (i + 1) b (bP P) P h1).symm
      rw [e]; exact hrefl _ _ _

end GlobalTheory.TwBridge
end

