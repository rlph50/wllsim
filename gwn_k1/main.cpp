#include <cstdlib>
#include <iostream>
#include <fstream>
#include <cstdio>
#include <complex.h>
#include <ctime>
#include <ratio>
#include <chrono>
#include <random>
#include <cmath>
#include <string.h>

#include <nlopt.h>
#include <fftw3.h>

using namespace std;

// SER_LEN is the max length of a series - used for initializing array sizes ec
#define SER_LEN 8190
// When we generate a new realisation, we generate then throw away the first GEN_SIZE points. This forms a run-in period for the process.
#define GEN_SIZE 1024
// used for setting array sizes etc
#define MAX_TRIALS 1000

// Next we use these as upper limits on the effort taken by the optimisation routines.
#define MAXTIME 15
#define MAXEVAL 1000
#define TOL 1.0e-8

// Variance Gamma Distribution parameters
#define VG_THETA (-0.5)
#define VG_NU 1.5
#define VG_SIGMA2 1



unsigned int ser_len=100; // actual length of series.

unsigned int which_min(double *x, unsigned int n) {
    double minVal=*x;
    int minIndex=0;
    for (unsigned int j=1;j<n;j++)
        if (x[j]<minVal) {
            minVal=x[j];
            minIndex=j;
            }
    return(minIndex);
    };
unsigned int which_max(double *x, unsigned int n) {
    double maxVal=*x;
    int maxIndex=0;
    for (unsigned int j=1;j<n;j++)
        if (x[j]>maxVal) {
            maxVal=x[j];
            maxIndex=j;
            }
    return(maxIndex);
    };

double digamma ( double x, int *ifault )
{
/******************************************************************************/
/*
  Purpose:

    DIGAMMA calculates DIGAMMA ( X ) = d ( LOG ( GAMMA ( X ) ) ) / dX

  Licensing:

    This code is distributed under the GNU LGPL license.

  Modified:

    20 March 2016

  Author:

    Original FORTRAN77 version by Jose Bernardo.
    C version by John Burkardt.

  Reference:

    Jose Bernardo,
    Algorithm AS 103:
    Psi ( Digamma ) Function,
    Applied Statistics,
    Volume 25, Number 3, 1976, pages 315-317.

  Parameters:

    Input, double X, the argument of the digamma function.
    0 < X.

    Output, int *IFAULT, error flag.
    0, no error.
    1, X <= 0.

    Output, double DIGAMMA, the value of the digamma function at X.
*/
  static double c = 8.5;
  static double euler_mascheroni = 0.57721566490153286060;
  double r;
  double value;
  double x2;
/*
  Check the input.
*/
  if ( x <= 0.0 )
  {
    value = 0.0;
    *ifault = 1;
    return value;
  }
/*
  Initialize.
*/
  *ifault = 0;
/*
  Use approximation for small argument.
*/
  if ( x <= 0.000001 )
  {
    value = - euler_mascheroni - 1.0 / x + 1.6449340668482264365 * x;
    return value;
  }
/*
  Reduce to DIGAMA(X + N).
*/
  value = 0.0;
  x2 = x;
  while ( x2 < c )
  {
    value = value - 1.0 / x2;
    x2 = x2 + 1.0;
  }
/*
  Use Stirling's (actually de Moivre's) expansion.
*/
  r = 1.0 / x2;
  value = value + log ( x2 ) - 0.5 * r;

  r = r * r;

  value = value
    - r * ( 1.0 / 12.0
    - r * ( 1.0 / 120.0
    - r * ( 1.0 / 252.0
    - r * ( 1.0 / 240.0
    - r * ( 1.0 / 132.0 ) ) ) ) );

  return value;
}

void ggbr_coef(unsigned int n, double d, double u, double *res) {
    // Populate "res" with n gegenbauer coefficients for d, u
    // implemented using the recursion formula for the coefficients.
    double ld, lu;

    ld=d;
    lu=u;
    res[0]=1.0l;
    res[1]=2.0l*ld*lu;
    res[2]=2.0l*ld*(1.0l+ld)*lu*lu-ld;
    for (unsigned int i=3;i<n;i++) {
        double temp=(ld-1.0l)/((double) i);
        res[i]=2.0l*lu*(temp+1.0l)*res[i-1]-(2.0l*temp+1.0l)*res[i-2];
        };
};

class cSimulate {
// This class generates a new realisation of a Gegenbauer white noise proces.
public:
    // variance-gamma distribution parameters
    // These are set to the estimated ones for the S&P data from Senata (2004)
    double vg_theta = VG_THETA, vg_nu = VG_NU, vg_sigma2 = VG_SIGMA2;

private:
    double d,u,sigma2,sigma, series_var;

    unsigned int n, gen_size;
    double *phi;
    double *p;
    unsigned int distribution=0; // Gaussian by default
    void calc_acf(unsigned int n1) {
        // calc Eqn 3.5 of Woodward, Cheng and Gray, 1998; Also Ford 1991.
        // Reverses Spectrum p to the underlying ACF via simple numerical integration- trapezoidal rule.
        unsigned int m=10000;
        for (unsigned int k=0; k<n1; k++) {
            long double y=0.0l, lastOmega=0.0l;
            long double lastPf=pow( 4.0l*(1.0l-u)*(1.0l-u), -d);
            for (unsigned int f=1; f<=m; f++) {
                long double f_n=((long double) f)/((long double) (2*m));
                long double omega=2.0l*M_PI*f_n;
                long double temp=cos(omega)-u;
                if (fabs(temp)>1.0e-200) {
                    long double Pf=pow(4.0l*temp*temp,-d)*cos(omega*((long double) k));
                    y+= (lastPf+Pf)/2.0l*(omega-lastOmega);
                    lastPf = Pf;
                    lastOmega = omega;
                    }
                };
            g[k]=y/M_PI;
            };
    };
    void acf_normalise() {
        // scale ACF so that first element is 1.0
        double g_max;
        g_max=fabs(*g);
        // Now scale everything down by g_max
        for (unsigned int i=0;i<2*gen_size;i++) g[i]=g[i]/g_max;
    };
    void DurbinLevinson() {
        // As documented by Hosking 1984 section 3.
        // Given an ACF, generate a process with that ACF.
        // We allow for a number of distributions.
        double Nt, Dt, m=0.0,v=1.0,sd=1.0;
        double *oldphi=(double *)malloc(gen_size*sizeof(double));
        unsigned seed1 = std::chrono::system_clock::now().time_since_epoch().count();
        std::mt19937_64 mersene_generator (seed1);  // mt19937 is a standard mersenne_twister_engine
        std::normal_distribution<double> xform_gaussian(0.0,1.0);
        std::student_t_distribution<double> xform_student(5.0);
        std::student_t_distribution<double> xform_student2(2.0);
        std::student_t_distribution<double> xform_student3(6.0);
        std::chi_squared_distribution<double> xform_chi_sq(1.0);
        std::chi_squared_distribution<double> xform_chi_sq3(3.0);
        std::uniform_real_distribution<double> uniform(-0.5,0.5);
        double gamma_alpha=0.25, gamma_beta=2.0;
        std::gamma_distribution<double> xform_gamma(gamma_alpha,gamma_beta);
        std::gamma_distribution<double> xform_gamma_changed(gamma_alpha/2.0,gamma_beta);
        double gamma_alpha_3=3.0, gamma_beta_3=2.0;
        std::gamma_distribution<double> xform_gamma3(gamma_alpha_3,gamma_beta_3);

        // Variance Gamma RVs
        // Using the algorithm documented by Madden Carr & Chung (1998)
        double vg_factor = 0.5*sqrt(vg_theta*vg_theta+2.0*vg_sigma2/vg_nu);
        double vg_mu_p = vg_factor+vg_theta/2.0;
        double vg_mu_n = vg_factor-vg_theta/2.0;
        double vg_nu_p = 1.0/(vg_mu_p*vg_mu_p*vg_nu);
        double vg_nu_n = 1.0/(vg_mu_n*vg_mu_n*vg_nu);
        double vg_sd   = sqrt(vg_theta*vg_theta*vg_nu+vg_sigma2);
        std::gamma_distribution<double> gamma_p(vg_mu_p,vg_nu_p);
        std::gamma_distribution<double> gamma_n(vg_mu_n,vg_nu_n);

        Nt=0.0; Dt=1.0;
        v=sigma2*series_var;

        if (distribution==0) {
            xform_gaussian.reset();
            y[0]=xform_gaussian(mersene_generator)*sqrt(v);
            }
        if (distribution==1)
            y[0]=xform_student(mersene_generator)/sqrt(5.0/3.0)*sqrt(v);
        if (distribution==2)
            y[0]=xform_chi_sq(mersene_generator)/sqrt(2.0)*sqrt(v);
        if (distribution==3)
            y[0]=xform_student2(mersene_generator)*sqrt(v);
        if (distribution==4) {
            xform_gaussian.reset();
            double temp=xform_gaussian(mersene_generator);
            y[0]=temp*temp*sqrt(v);
            }
        if (distribution==5)
            y[0]=xform_chi_sq3(mersene_generator)/sqrt(6.0)*sqrt(v);
        if (distribution==6)
            y[0]=(gamma_p(mersene_generator)-gamma_n(mersene_generator))/vg_sd*sqrt(v);
        if (distribution==7)
            y[0]= (xform_gamma(mersene_generator)-/*mean*/ gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta)*sqrt(v);
        if (distribution==8) {
            // Laplace distribution. We generate this directly from the Uniform Distribution.
            double u = uniform(mersene_generator);
            double sign_u = 1.0;
            if (u<0.0) sign_u = (-1);
            double laplace_rv = -sign_u/sqrt(2.0l)*log(1.0-2.0*fabs(u));
            y[0]= laplace_rv*sqrt(v);
            }
        if (distribution==9)
            y[0]=xform_student3(mersene_generator)*sqrt(v)/sqrt(6.0/4.0);
        if (distribution==10)
            y[0]= (xform_gamma(mersene_generator)-/*mean*/ gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta)*sqrt(v);
        if (distribution==11)
            y[0]= (xform_gamma3(mersene_generator)-/*mean*/ gamma_alpha_3/gamma_beta_3)/(sqrt(gamma_alpha_3)*gamma_beta_3)*sqrt(v);

        for (unsigned int t=1;t<gen_size;t++) {
            double sum=0.0;
            for (unsigned int j=0;j<t;j++) oldphi[j]=phi[j];
            for (unsigned int j=1;j<t;j++) sum+=(oldphi[j]*g[t-j]);
            Dt-=Nt*Nt/Dt;
            Nt=g[t]-sum;
            phi[t]=Nt/Dt;
            for (unsigned int j=1;j<t;j++)
                phi[j]=oldphi[j] - (phi[t]*oldphi[t-j]);
            m=0.0;
            for (unsigned int j=1;j<=t;j++) m+=(phi[j]*y[t-j]);
            v*=(1-phi[t]*phi[t]);
            sd=sqrt(v);
            if (distribution==0)
                y[t]=(xform_gaussian(mersene_generator)*sd)+m;
            if (distribution==1)
                y[t]=(xform_student(mersene_generator)/sqrt(5.0/3.0)*sd)+m;
            if (distribution==2)
                y[t]=(xform_chi_sq(mersene_generator)/sqrt(2.0)*sd)+m;
            if (distribution==3)
                y[t]=(xform_student2(mersene_generator)*sd)+m;
            if (distribution==4) {
                double temp=xform_gaussian(mersene_generator);
                y[t]=temp*temp*sd+m;
                }
            if (distribution==5)
                y[t]=(xform_chi_sq3(mersene_generator)/sqrt(6.0)*sd)+m;
            if (distribution==6)
                y[t]=(gamma_p(mersene_generator)-gamma_n(mersene_generator))/vg_sd*sd+m;
            if (distribution==7)
                y[t]= ((xform_gamma(mersene_generator)-/*mean*/ gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta))*sd+m;
            if (distribution==8) {
                // Laplace distribution. We generate this directly from the Uniform Distribution.
                double u = uniform(mersene_generator);
                double sign_u = 1.0;
                if (u<0.0) sign_u = (-1);
                double laplace_rv = -sign_u/sqrt(2.0l)*log(1.0-2.0*fabs(u));
                y[t] = laplace_rv*sd + m;
                }
            if (distribution==9)
                y[t]=xform_student3(mersene_generator)/sqrt(6.0/4.0)*sd+m;
            if (distribution==10) {
                if (t<=(n/2)+(GEN_SIZE/4))
                    y[t]= ((xform_gamma(mersene_generator)-/*mean*/ gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta))*sd+m;
                else
                    y[t]= ((xform_gamma_changed(mersene_generator)-/*mean*/ 0.5*gamma_alpha/gamma_beta)
                            /(sqrt(gamma_alpha/2.0)*gamma_beta))*sd+m;
            }
            if (distribution==11)
                y[t]= (xform_gamma3(mersene_generator)-/*mean*/ gamma_alpha_3/gamma_beta_3)/(sqrt(gamma_alpha_3)*gamma_beta_3)*sd+m;
          };
        free(oldphi);
    };


public:
    double *y, g[2*SER_LEN+2];
    cSimulate(int init_n, double init_d, double init_u, double init_sigma2, unsigned int init_dist) {
        // Algorithm here is that we generate GEN_SIZE+SER_LEN obs but for half the power function.
        // otherwise power function repeats itself.
        n=init_n;
        gen_size=n+GEN_SIZE;
        d=init_d;
        u=init_u;
        sigma2=init_sigma2;
        sigma=sqrt(sigma2);
        distribution=init_dist;
        y=(double *)malloc(gen_size*sizeof(double));
        phi=(double *)malloc(gen_size*sizeof(double));
        for (unsigned int i=0;i<gen_size;i++) y[i]=phi[i]=0.0;
        for (unsigned int i=0;i<2*ser_len+2;i++) g[i]=0.0;
        calc_acf(gen_size);
        series_var=g[0];    // save for later
        acf_normalise();
        };
    ~cSimulate() {
        free(y);
        free(phi);
        };
    void GenerateProcess() {
        DurbinLevinson();
        if (GEN_SIZE>0) {
            for (unsigned int i=0;i<n;i++) y[i]=y[i+(GEN_SIZE/4)];
            for (unsigned int i=n;i<n+(GEN_SIZE/2);i++) y[i]=0.0;
            }
        }
};

// Use Standard C Routines for NLOPT interface.
typedef struct {
    unsigned int n, m, n_calls;
    double *spec, *y, *cos_2_pi_f, *logSpec, u, d, sigma2;
    } seriesParams;

class cSeriesStats {
// part of estimation process - find series stats - acf periodogram etc.
// we use a standard object in part to ensure all the estimation methods have exactly the same stats to work with,
// and they have exactly the same overhead in terms of producing those stats.
public:
    int n, m, nm, kn;
    bool est_u, est_d, est_sigma2, est_with_delta;
    double *freq, *cos_2_pi_f, *spec, *logSpec, *aggSpec, *logAggSpec, *cos_2_pi_fk, *y, *g;

    cSeriesStats(unsigned int init_n, double *init_y, int smoothing) {
        y=init_y;
        n=init_n;
        m=smoothing;    // smoothing is the number of periodogram points to average (sum) over.
        if (m>0) {
            kn=n/(2*m);
            nm=2*m*kn;
            }
        else {
            kn=n/2;
            nm=2*kn;
            };

        freq=(double *)malloc(n*sizeof(double));
        spec=(double *)malloc(n*sizeof(double));
        cos_2_pi_f=(double *)malloc(n*sizeof(double));
        logSpec=(double *)malloc(n*sizeof(double));
        aggSpec=(double *)malloc((n+1)*sizeof(double));
        logAggSpec=(double *)malloc((n+1)*sizeof(double));
        cos_2_pi_fk=(double *)malloc((n+1)*sizeof(double));
        g=(double *)malloc(n*sizeof(double));
        calcACF();
        calcSpectrum();
        if (m>0)
            calcAggSpec();
       };
    ~cSeriesStats() {
        free(freq);
        free(spec);
        free(cos_2_pi_f);
        free(logSpec);
        free(aggSpec);
        free(logAggSpec);
        free(cos_2_pi_fk);
        free(g);
        };
    void calcSpectrum() {
        fftw_complex *in, *out;
        fftw_plan plan;
        in = (fftw_complex*) fftw_malloc(sizeof(fftw_complex) * SER_LEN);
        for (int i=n-1;i>=0;i--) {in[i][0]=y[i]; in[i][1]=0.0;};
        out = (fftw_complex*) fftw_malloc(sizeof(fftw_complex) * SER_LEN);
        plan = fftw_plan_dft_1d(n, in, out, FFTW_FORWARD, FFTW_ESTIMATE);
        fftw_execute(plan);
        for (int i=0;i<n;i++) {
            freq[i]=((double) i)/((double) n);
            cos_2_pi_f[i]=cos(2.0*M_PI*freq[i]);
            //cout << i << " " << freq[i] << " " << cos_2_pi_f[i] << endl;
            spec[i]=(out[i][0]*out[i][0]+out[i][1]*out[i][1])/(2.0*M_PI*((double) n));
            logSpec[i]=log(spec[i]);
            };
        fftw_destroy_plan(plan);
        fftw_free(in); fftw_free(out);
        //cout << endl << endl << endl;
    };

    void calcAggSpec(){
        // as per paper. We aggregate together periodogram ordinates
        for (int k=1;k<=kn;k++) {
            double sum=0.0;
            int mk=m*k;
            for (int j=m*(k-1)+1; j<=mk; j++)
                sum+=spec[j];
            aggSpec[k-1]=sum; ///dm;
            logAggSpec[k-1]=log(aggSpec[k-1]);
            cos_2_pi_fk[k-1]= cos(M_PI*((double) (2*k-1))/((double) (2*kn)));
        }
    };

    double mean() {
        double sum=y[0];
        for (int i=1;i<n;i++) sum+=y[i];
        return(sum/((double) n));
        };

    double processVar() {
        double m=mean();
        double sum=0.0l;
        for (int i=0;i<n;i++) {
            double temp=y[i]-m;
            sum+= temp*temp;
            }
        sum/=((double) n);
        return(sum);
    };

    void calcACF() {
        double m=mean();
        for (int k=0;k<n;k++) g[k]=0.0;
        for (int k=0;k<n/2;k++) {
            double sum=0.0l;
            unsigned int nk= n;
            for (unsigned int i=0;i<nk;i++) sum+= (y[i]-m)*(y[(i+k)%n]-m);
            g[k]=sum/((double) nk);
            }
    };
};

class cCSSEst {
// Estimate parameters of a realisation using methof of Chung (1996)
private:
    double *y;  // pointer to array of realisations.
    double calc_d, calc_u, calc_sigma2, calc_min_lse;
    unsigned int n;
    cSeriesStats *ss;

    static void calc_ma_errors(unsigned int n, double d, double u, double *y, double *eps) {
        // This routine reverses the "y" realisations to find the errors
        // under the assumption that the process is ggbr white noise.
        double *c=(double *)malloc(sizeof(double)*n);
        double sum;

        ggbr_coef(n,d,u, c);

        eps[0]=y[0]; // We assume c[0]==1.0!
        for (unsigned int t=1;t<n;t++) {
            sum=0.0l;
            for (unsigned int j=1;j<=t;j++)
                sum+=c[j]*eps[t-j];
            eps[t]=(y[t]-sum); // divide by c[0] but this is 1..
            };
        free(c);
    };

    static double css_lse(unsigned dimSize, const double* x, double* grad, void* f_data){
        // Calculate the lse - "S" function in Chungs notation.
        // This is the function to be minimised.
        double d=x[0], u=x[1]; //, sigma2=x[2];
        // Check parameters are within range; if not then move them so they are
        if (u>1.0) u=1.0;
        if (u<-1.0) u=-1.0;
        if (d<0.0) d=1.0e-20;
        if (d>0.5) d=0.5-1.0e-20;
        //if (sigma2<1.0e-20)  sigma2=1.0e-20;
        double res;
        seriesParams *sp1 = (seriesParams *) f_data;
        unsigned int n=sp1->n;
        //double dn2=((double) n)/2.0;
        double *y=sp1->y;

        res=0.0l;
        double *eps=(double *)malloc(sizeof(double)*n);
        calc_ma_errors(n,d,u,y, eps);
        for (unsigned int i=1;i<n-1;i++) {
            double temp=eps[i];
            if (!isnan(temp)) res+=temp*temp;
            }
        free(eps);
        if (isnan(res))
            cerr << "CSS LSE NAN\n";
        if (fabs(res)>1.0e20)
            cerr << "CSS LSE 1e20\n";
        //double logSigma2=log(sigma2);
        //double log2pi=log(2.0*M_PI);
        return (res);
    };
public:
    seriesParams sp;
    nlopt_result optResult;
    double timeTaken=0.0;

    cCSSEst(unsigned int init_n, double *init_y) {
        y=init_y;
        n=init_n;
        ss = new cSeriesStats(init_n, init_y, 0);
        sp.y=init_y;
        sp.n=init_n;
        findMinLSE();
       };
    ~cCSSEst() {
        ss->~cSeriesStats();
    };
    void findMinLSE() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.0};
        double ub[]={1.0-1.0e-20,1};

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,2);
        nlopt_set_min_objective(directOpt, css_lse, (void *) &sp);
        nlopt_set_lower_bounds(directOpt, lb);
        // DIRECT algorithm requires a bounded parameter space
        // So we need to restrict an upper bound of the variance.
        // to do this we use the variance of teh series as a whole as an upper bound.
        //ub[2]=ss->processVar();
        nlopt_set_upper_bounds(directOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,2);
        nlopt_set_min_objective(cobyLAOpt, css_lse, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        // reset the upper bound of the variance
        //ub[2]=HUGE_VAL;
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d=x[0];
        calc_u=x[1];
        //calc_sigma2=x[2];
        calc_sigma2 = lse_val_c / ((double) n);
        calc_min_lse=lse_val_c;

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();
    };
    double Optimal_d() {return(calc_d);};
    double Optimal_u() {return(calc_u);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cWHTLEst {
// Estimate parameters of a realisation using methof of Whittle as documented by Giraitis and Leipus (1995)
// and Ford (1991).
private:
    double *y;  // pointer to array of realisations.
    double calc_d, calc_u, calc_sigma2, calc_min_lse;
    unsigned int n, m;
    cSeriesStats *ss;

    static double spectral_density(double cos_omega, double d, double u) {
        // returns the value of the spectral density of a ggbr white noise process at a given frequency (cos_omega).
        // used by the "whittle_log_liklihood" function
        double temp=cos_omega-u;
        double temp2;
        if (fabs(temp)<1.0e-20)
            temp2=0;
        else
            temp2=pow(4.0*temp*temp,-d);
        return(temp2);
        //return(sigma2/(2.0*M_PI) * temp2);
        }
    static double whittle_log_likelihood(unsigned dimSize, const double* x, double* grad, void* f_data){
        // This calculates the Whittle Log Liklihood, to be minimised to produce the parameter estimates.
        double d;
        double u;
        //double sigma2;
        d=x[0];u=x[1];//sigma2=x[2];
        if (u>1.0) u=1.0-1.0e-20;
        if (u<0.0) u=0.0;
        if (d<0.0) d=1.0e-20;
        if (d>0.5) d=0.5-1.0e-20;
        //if (sigma2<1.0e-20)  sigma2=1.0e-20;
        double res;
        seriesParams *sp1 = (seriesParams *) f_data;
        unsigned int n=sp1->n;

        res=0.0;
        for (unsigned int i=0;i<n;i++) {
            double f=spectral_density(sp1->cos_2_pi_f[i], d, u);
            if ((f>1.0e-20)&&!isnan(f)&&!isinf(f))
                res+= (sp1->spec[i])/f;
            }
        if (isnan(res)||isinf(res))
            cerr << "Whittle NAN\n";
        if (fabs(res)>1.0e20)
            cerr << "Whittle 1e20\n";
        return (-res/((double) n));
        };

public:
    seriesParams sp;
    nlopt_result optResult;
    double timeTaken=0.0;

    cWHTLEst(unsigned int init_n, double *init_y, int smoothing) {
        y=init_y;
        n=init_n;
        m=smoothing;
        if ((m<=0)|(m>(init_n/2))) m=1;
        ss = new cSeriesStats(init_n, init_y, m);
        sp.n=(m>1 ? (ss->kn):init_n);
        sp.m=smoothing;
        sp.y=init_y;
        sp.cos_2_pi_f=(m>1 ? (ss->cos_2_pi_fk):(ss->cos_2_pi_f));
        sp.spec=(m>1 ? ss->aggSpec:ss->spec);
        sp.logSpec=(m>1 ? ss->logAggSpec:ss->logSpec);
        findMaxLL();
       };
    ~cWHTLEst() {
        ss->~cSeriesStats();
    };

    void findMaxLL() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.0};
        double ub[]={0.5-1.0e-20,1.0};

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,2);
        nlopt_set_max_objective(directOpt, whittle_log_likelihood, (void *) &sp);
        nlopt_set_lower_bounds(directOpt, lb);
        // DIRECT algorithm requires a bounded parameter space
        // So we need to restrict an upper bound of the variance.
        // to do this we use the variance of teh series as a whole as an upper bound.
        //ub[2]=ss->processVar();
        nlopt_set_upper_bounds(directOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,2);
        nlopt_set_max_objective(cobyLAOpt, whittle_log_likelihood, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        // reset the upper bound of the variance
        //ub[2]=HUGE_VAL;
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d=x[0];
        calc_u=x[1];
        //calc_sigma2=x[2];
        //cout << lse_val_c << endl;
        calc_sigma2 = 2.0*M_PI*(-lse_val_c);
        calc_min_lse=lse_val_c;

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();
    };
    double Optimal_d() {return(calc_d);};
    double Optimal_u() {return(calc_u);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cBNPEst {
// This implements the new estimator for the parameters.
public:
    seriesParams sp;
    cSeriesStats *ss;

    unsigned int n;
    double opt_lse;
    double timeTaken=0.0;
    double calc_sum_xj_sq=0.0;

    static double lse(unsigned dimSize, const double* x, double* grad, void* f_data){
        // This is the L" function of the paper - the sum of squares between the periodogram and the spectral density
        // assuming a ggbr white noise spectral density.
        double d, u, sigma2;
        double res=0.0;
        seriesParams *sp1 = (seriesParams *) f_data;
        (sp1->n_calls)++;
        unsigned int n=(sp1->n); //This "n" is reset to be the number of periodogram entries - it is not the data size.

        d=x[0];u=x[1];sigma2=x[2];
        if (isnan(d)) return(d);
        if (isnan(u)) return(u);
        if (isnan(sigma2)) return(sigma2);

        if (u>1.0) u=1.0;
        if (u<0.0) u=0.0;
        if (d<0.0) d=1.0e-20;
        if (d>0.5) d=0.5-1.0e-20;
        if (sigma2<1.0e-20) sigma2=1.0e-20;

        double logSigma2=log(sigma2/(2.0*M_PI));

        double *cos_2_pi_f=sp1->cos_2_pi_f;
        double *logSpec=sp1->logSpec;

        for (unsigned int i=1;i<n;i++) {
            double temp1=cos_2_pi_f[i]-u;
            if (fabs(temp1)>=1.0e-100) {
                double temp2=log(4.0*temp1*temp1);
                double temp3=logSpec[i] - (logSigma2-d*temp2);
                if (isnan(temp3))
                    cerr << "BNP LSE temp3 NAN logSpec["<<i<<"]="<<logSpec[i]<<" d=" << d<< " sigma2=" << sigma2 << " logSigma2="<< logSigma2<<" temp2="<<temp2<<" temp1="<<temp1<<endl;
                res+= temp3*temp3;
                }
            };
        if (res<0.0)
            cerr << "res<0\n";
        res=sqrt(fabs(res));
        if (isnan(res))
            cerr << "BNP LSE NAN\n";
        if (fabs(res)>1.0e100)
            cerr << "BNP LSE " << res << endl;
        return (res);
    };

private:
    double calc_u=0.0, calc_d=0.0, calc_sigma2=1.0, calc_min_lse=0.0;
    int m, kn, nm;

nlopt_result findMinLSE() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5,0.5};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.05,1.0e-20};
        double ub[]={0.5-1.0e-20,0.95,HUGE_VAL};
        int ifault=0;

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,3);
        nlopt_set_min_objective(directOpt, lse, (void *) &sp);
        nlopt_set_lower_bounds(directOpt, lb);
        // DIRECT algorithm requires a bounded parameter space
        // So we need to restrict an upper bound of the variance.
        // to do this we use the variance of teh series as a whole as an upper bound.
        ub[2]=ss->processVar();
        nlopt_set_upper_bounds(directOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,3);
        nlopt_set_min_objective(cobyLAOpt, lse, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        // reset the upper bound of the variance
        ub[2]=HUGE_VAL;
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d=x[0];
        calc_u=x[1];
        calc_sigma2=x[2];
        calc_min_lse=lse_val_c;

        /* this needed for the theoretical variance calc.*/
        calc_sum_xj_sq=0.0;
        for (unsigned int i=1;i<n;i++) {
            double temp1=sp.cos_2_pi_f[i]-0.8;
            if (fabs(temp1)>=1.0e-20) {
                double temp2=log(4.0*temp1*temp1);
                calc_sum_xj_sq+=temp2*temp2;
                }
            }
//        for (unsigned int i=0;i<n;i++) cout << sp.cos_2_pi_f[i] << endl;
//        cout << endl << endl << endl;
//cout << sp.cos_2_pi_f[0] << " " << sp.cos_2_pi_f[1] << " " << sp.cos_2_pi_f[2] << " " << calc_sum_xj_sq << endl;

        // Correction for bias in sigma2 estimate - refer to paper.
        double bias=exp(-digamma((double) m,&ifault));
        calc_sigma2 = calc_sigma2*bias;
        // cout << calc_sigma2 << endl;

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();
//cout  << timeTaken << endl;
        return(optResult);
    };

public:
    double *y;
    nlopt_result optResult, optResult2;

    cBNPEst(int init_n, double *py, int smoothing) {
        y=py;
        m=smoothing;
        if ((m<=0)|(m>(init_n/2))) m=1;
        ss = new cSeriesStats(init_n, py, m);
        n=init_n;
        sp.n=(m>1 ? (ss->kn):init_n);
        sp.m=smoothing;
        sp.y=py;
        sp.cos_2_pi_f=(m>1 ? (ss->cos_2_pi_fk):(ss->cos_2_pi_f));
        sp.logSpec=(m>1 ? ss->logAggSpec:ss->logSpec);
        sp.n_calls=0;
        optResult=findMinLSE();
    };
    ~cBNPEst() {
        ss->~cSeriesStats();
    };
    double Optimal_d() {return(calc_d);};
    double Optimal_u() {return(calc_u);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cRes {
// This class stores the parameter estimates.
// We instantiate this multiple times to store the results from each of the various methods.
private:
    unsigned int maxTrials, nTrials;
    nlopt_result *optRes;
    double *d_Res, *u_Res, *sigma2_Res, *timeRes;
    bool *Err;
    double true_d, true_u, true_sigma2;
    string name;

public:
    double theoretical_sigma2_d=0.0;
    cRes() {
        d_Res=NULL;
        u_Res=NULL;
        sigma2_Res=NULL;
        timeRes=NULL;
        optRes=NULL;
        Err=NULL;
    }; // default constructor
    ~cRes() {
        if (optRes!=NULL) free(optRes);
        if (d_Res!=NULL) free(d_Res);
        if (u_Res!=NULL) free(u_Res);
        if (sigma2_Res!=NULL) free(sigma2_Res);
        if (timeRes!=NULL) free(timeRes);
        if (Err!=NULL) free(Err);
    };
    void Init(unsigned int init_maxTrials, string init_name, double init_d, double init_u, double init_sigma2) {
        maxTrials=init_maxTrials;
        name=init_name;
        true_d=init_d;
        true_u=init_u;
        true_sigma2=init_sigma2;
        nTrials=0;
        optRes=(nlopt_result *)malloc(sizeof(nlopt_result)*maxTrials);
        d_Res=(double *)malloc(sizeof(double)*maxTrials);
        u_Res=(double *)malloc(sizeof(double)*maxTrials);
        sigma2_Res=(double *)malloc(sizeof(double)*maxTrials);
        timeRes=(double *)malloc(sizeof(double)*maxTrials);
        Err=(bool *)malloc(sizeof(bool)*maxTrials);
        for (unsigned int i=0;i<maxTrials;i++) {
            optRes[i]= (nlopt_result)0;
            d_Res[i]=0.0;
            u_Res[i]=0.0;
            sigma2_Res[i]=0.0;
            timeRes[i]=0.0;
            Err[i]=false;
            };
    };
    string result() {
        string txt;
        char cRes1[4096];


        if (theoretical_sigma2_d>0.0001)
            sprintf(cRes1, "%s,%0.2f,%0.2f,Bias,%0.4f,%0.4f,%0.4f,%0.6f\n,,,RMSE,%0.4f,%0.4f,%0.4f\n,,,True se2,%0.4f\n",
                name.data(), true_d, true_u,
                true_d-d_Mean(), true_u-u_Mean(), true_sigma2-sigma2_Mean(), meanTime(),
                d_RMSE(), u_RMSE(), sigma2_RMSE(),
                theoretical_sigma2_d
                );
        else
            sprintf(cRes1, "%s,%0.2f,%0.2f,Bias,%0.4f,%0.4f,%0.4f,%0.6f\n,,,RMSE,%0.4f,%0.4f,%0.4f\n",
                name.data(), true_d, true_u,
                true_d-d_Mean(), true_u-u_Mean(), true_sigma2-sigma2_Mean(), meanTime(),
                d_RMSE(), u_RMSE(), sigma2_RMSE()
                );
        txt=cRes1;
        return(txt);
        };
    double d_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=d_Res[i]; n++;}
        return (tot/((double) n));
    };
    double u_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=u_Res[i]; n++;}
        return (tot/((double) n));
    };
    double sigma2_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=sigma2_Res[i]; n++;}
        return (tot/((double) n));
    };
    double d_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (d_Res[i]-true_d)*(d_Res[i]-true_d);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double u_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (u_Res[i]-true_u)*(u_Res[i]-true_u);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double sigma2_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (sigma2_Res[i]-true_sigma2)*(sigma2_Res[i]-true_sigma2);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double totalTime() {
        double tot=0.0;
        for (unsigned int i=0;i<nTrials;i++) tot+=timeRes[i];
        return (tot);
    };
    double meanTime() {return(totalTime()/((double) nTrials));};
    int Err_Count() {
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if (Err[i]) n++;
        return(n);
    };
    void addNewResult() {
        optRes[nTrials]=(nlopt_result)0;
        d_Res[nTrials]=0.0;
        u_Res[nTrials]=0.0;
        sigma2_Res[nTrials]=0.0;
        timeRes[nTrials]=0.0;
        Err[nTrials]=false;
        nTrials++;
        };
    void addResult(double d, double u, double sigma2, nlopt_result opt,double timeTkn) {
        optRes[nTrials-1]=opt;
        d_Res[nTrials-1]=d;
        u_Res[nTrials-1]=u;
        sigma2_Res[nTrials-1]=sigma2;
        timeRes[nTrials-1]=timeTkn;
    };
    void addErr() {Err[nTrials-1]=true;};
};

class cMonteCarloTrials {
// This class runs the trials, for a given set of "true" parameter estimates.
private:
    unsigned int nTrials, dist;
    double true_d;
    double true_u;
    double true_sigma2;
    double calc_sum_xj_sq;
public:
    cRes BNPRes, BNPRes2, BNPRes3, CSSRes, WhittleRes;
    cMonteCarloTrials(unsigned int init_nTrials, double init_d, double init_u, double init_sigma2, unsigned int init_dist) {
        nTrials=init_nTrials;
        true_d=init_d;
        true_u=init_u;
        true_sigma2=init_sigma2;

        dist=init_dist;
        BNPRes.Init(nTrials,"BNP",true_d,true_u,true_sigma2);
        BNPRes2.Init(nTrials,"BNP2",true_d,true_u,true_sigma2);
        BNPRes3.Init(nTrials,"BNP3",true_d,true_u,true_sigma2);
        CSSRes.Init(nTrials,"CSS",true_d,true_u,true_sigma2);
        WhittleRes.Init(nTrials,"Whittle",true_d,true_u,true_sigma2);
    };
    string Summary() {
        string txt;
        txt=  BNPRes.result()
            + BNPRes2.result()
            + BNPRes3.result()
            + CSSRes.result()
            + WhittleRes.result()
            ;
        return(txt);
    };
    void runTrials() {
        // Set up our Simulation object;
        cSimulate cs(ser_len, true_d, true_u, true_sigma2, dist);
        for (unsigned int trial=0;trial<nTrials;trial++) {
            cs.GenerateProcess();

            BNPRes.addNewResult();
            BNPRes2.addNewResult();
            BNPRes3.addNewResult();
            CSSRes.addNewResult();
            WhittleRes.addNewResult();

            cBNPEst BNPEst(ser_len, cs.y, 1);
            if ((BNPEst.optResult<0)||(BNPEst.optResult==NLOPT_MAXTIME_REACHED)) BNPRes.addErr();
            else BNPRes.addResult(BNPEst.Optimal_d(),BNPEst.Optimal_u(),BNPEst.Optimal_sigma2(),BNPEst.optResult,BNPEst.timeTaken);
            // save extra calc away as well for output
            if ((dist==0)&(BNPEst.calc_sum_xj_sq>0.0001))
                BNPRes.theoretical_sigma2_d=M_PI*M_PI/(6.0*sqrt(BNPEst.calc_sum_xj_sq));

            cBNPEst BNPEst2(ser_len, cs.y, 2);
            if ((BNPEst2.optResult<0)||(BNPEst2.optResult==NLOPT_MAXTIME_REACHED)) BNPRes2.addErr();
            else BNPRes2.addResult(BNPEst2.Optimal_d(),BNPEst2.Optimal_u(),BNPEst2.Optimal_sigma2(),BNPEst2.optResult,BNPEst2.timeTaken);

            cBNPEst BNPEst3(ser_len, cs.y, 3);
            if ((BNPEst3.optResult<0)||(BNPEst3.optResult==NLOPT_MAXTIME_REACHED)) BNPRes3.addErr();
            else BNPRes3.addResult(BNPEst3.Optimal_d(),BNPEst3.Optimal_u(),BNPEst3.Optimal_sigma2(),BNPEst3.optResult,BNPEst3.timeTaken);

            cCSSEst CSSEst(ser_len, cs.y);
            if ((CSSEst.optResult<0)||(CSSEst.optResult==NLOPT_MAXTIME_REACHED)) CSSRes.addErr();
            else CSSRes.addResult(CSSEst.Optimal_d(), CSSEst.Optimal_u(), CSSEst.Optimal_sigma2(),CSSEst.optResult,CSSEst.timeTaken);

            cWHTLEst WHTLEst(ser_len, cs.y,1);
            if ((WHTLEst.optResult<0)||(WHTLEst.optResult==NLOPT_MAXTIME_REACHED)) WhittleRes.addErr();
            else WhittleRes.addResult(WHTLEst.Optimal_d(), WHTLEst.Optimal_u(), WHTLEst.Optimal_sigma2(),WHTLEst.optResult,WHTLEst.timeTaken);

       };
    };
};


int main(int argc, char* argv[])
{
    string infoStr="Gegenbauer Series Simulations.\narg[1] = Series length\narg[2] = Series Variance\narg[3] = (cosine of) Gegenbauer Frequency (u)\narg[4] = Series distribution - one of gauss, chisq, student, tdist, tdist2\n\n";


    unsigned int dist=0;
    double d,u=0.8,sigma2=1.0;

    if (argc<=1) {
        cout << infoStr;
        return(0);
        };

    if (argc>1) {
        if ((strcmp(argv[1],"-h")==0)||(strcmp(argv[1],"-help")==0)||(strcmp(argv[1],"-?")==0)) {
            cout << infoStr;
            return(0);
            }
        };

    if (argc>1) {
        int n;
        sscanf(argv[1], "%d", &n);
        if ((n<50)||(n>SER_LEN)) {
            cerr << "Invalid Series Length: " << argv[1] <<endl << "Series Length set to " << SER_LEN << endl;
            ser_len=SER_LEN;
            }
        else ser_len=n;
        };

    if (argc>2) {// sigma2
        double sig2;
        sscanf(argv[2], "%lf", &sig2);
        if (sig2<=0.0) {
            cerr << "Invalid variance: " << argv[2] <<endl << "Series variance set to 1.0" << endl;
            sigma2=1.0;
            }
        else sigma2=sig2;
        };

    if (argc>3) {// u
        sscanf(argv[3], "%lf", &u);
        if ((u<=-1.0)||(u>=1.0)) {
            cerr << "Invalid Gegenbauer Frequency: " << argv[3] <<endl << "Gegenbauer Frequency set to 0.2" << endl;
            u=0.2;
            }
        };

    if (argc>4) {
        if (strcmp(argv[4],"gauss")==0)
            dist=0;
        if (strcmp(argv[4],"chisq")==0)
            dist=2;
        if (strcmp(argv[4],"student")==0)
            dist=1;
        if (strcmp(argv[4],"tdist")==0)
            dist=1;
        if (strcmp(argv[4],"tdist2")==0)
            dist=3;
        if (strcmp(argv[4],"t-dist")==0)
            dist=1;
        if (strcmp(argv[4],"sq-gauss")==0)
            dist=4;
        if (strcmp(argv[4],"chisq3")==0)
            dist=5;
        if (strcmp(argv[4],"vg")==0)
            dist=6;
        if (strcmp(argv[4],"gamma")==0)
            dist=7;
        if (strcmp(argv[4],"laplace")==0)
            dist=8;
        if (strcmp(argv[4],"tdist3")==0)
            dist=9;
        if (strcmp(argv[4],"change")==0)
            dist=10;
        if (strcmp(argv[4],"gamma3")==0)
            dist=11;
        };

    cout << "Running " << MAX_TRIALS << " trials of length " << ser_len << " from ";
    if (dist==0)
        cout << "Gaussian";
    if (dist==1)
        cout << "Student t-dist(df=5)";
    if (dist==2)
        cout << "Chi-Sq(df=1)";
    if (dist==3)
        cout << "Student t-dist(df=2)";
    if (dist==4)
        cout << "Gaussian-Squared";
    if (dist==5)
        cout << "Chi-Sq(df=3)";
    if (dist==6)
        cout << "Variance-Gamma(" << VG_THETA << "," << VG_NU << "," << VG_SIGMA2 << ")";
    if (dist==7)
        cout << "Gamma(0.5,0.5)";
    if (dist==8)
        cout << "Laplace";
    if (dist==9)
        cout << "Student t-dist(df=6)";
    if (dist==10)
        cout << "Gamma Changing";
    if (dist==11)
        cout << "Gamma(3,2)";
    cout << " distribution with u=" << u << endl << endl;

    cout << "Method,d,u,,Est d,Est u,Est s2,Avg Time\n";
    for (d=0.15;d<0.46;d+=0.15)
        {
            if (dist==6)
                sigma2 = VG_THETA*VG_THETA*VG_NU+VG_SIGMA2;
            cMonteCarloTrials mct(MAX_TRIALS, d, u, sigma2, dist);
            mct.runTrials();
            cout << mct.Summary();
            cout.flush();
            };

    return 0;
}
