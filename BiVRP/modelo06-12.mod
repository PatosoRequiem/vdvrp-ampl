
#CONJUNTOS 
set N;					     #Numero de nodos de la red
set A:= {i in N, j in N: i!=j};			     #Arcos de la red
set K;				         #Numero de vehiculos
set P; 						 #Numero de periodos o intervalos termporales considerados para cada arco
set V;						 #numero de vueltas
#----------------------------------------------------------------------------------------------------------------------------------------------------------
#PARAMETROS PRINCIPALES
param O;							#inicio
param q;							#capacidad del vehiculo
param d{i in N} ;					#demanda del cliente i
param LI {p in P};					#limite inferiores del intervalo p
param LS{p in P};					#limite superior del intervalo p
param B1 default 100000;			#numero muy grande
param B2 default 100000;			#numero muy grande


#PARAMETROS DE EMISION
param e{i in N, j in N, p in P} ; #emision en el arco i,j emitida por el vehiculo K			FLOTA HOMOGENEA
param ee{j in N, p in P} ;			#emision producida por zonas de espera del vehiculo K	FLORA HOMOGENEA


#PARAMETROS DE COSTOS
param g{i in N, j in N , p in P};	#costo de circular por el arco i,j en el momento del dia CONSULTAR
param gg{j in N, p in P} 	 ;  #costo por detencion en el periodo m,  CONSULTAR SI ES CON PERIODO.

#PARAMETROS DE TIEMPO
param T{i in N,j in N, p in P} ;  #tiempo de desplazarse de i a j en el momento p
param tt{j in N, p in P} ; 		#tiempo de servicio en el nodo j en el periodo m TIEMPO DE ATENCION VERTICAL

########################################################################################################
/* Conjuntos, Parametros y Variables para la normalización */

param cantobj := 2						;	# cantidad de objetivos del problema
param cantejc := 9						;	# cantidad de ejecuciones para la frontera de pareto recomendacion 11 valor cercano a 0

set objetivos := {1..cantobj}			;	# conjunto de objetivos del problema
set ejecuciones := {1..cantejc}			;	# conjunto de ejecuciones para la frontera de pareto

param h default 0 						;	# identifica un objetivo en particular
param sigma{ejecuciones,objetivos}		;	# ponderadores para la frontera de pareto de este obtengo en valor de betha
param betha{objetivos} default 0		;	# ponderadores de cada objetivo sirve para el .run

param MV{objetivos} default 999999999	;	# mejor valor alcanzado por cada objetivo
param PV{objetivos} default 0	;	# peor valor alcanzado por cada objetivo
param TDP := 0;
#----------------------------------------------------------------------------------------------------------------------------------------------------------
#VARIABLES DEL PROBLEMA
var X{i in N, j in N, p in P, v in V, k in K:i!=j} binary;	#1 si el vehiculo viaja entre los nodos ij saliendo con el camion k,  en el intervalo P
var Y{j in N, v in V, k in K} binary;						#1 si el cliente j es atendido por el camion k
var t{i in N, v in V, k in K}>=0 ;							#tiempo de partida del cliente j, con el camion k en la vuelta v (agregar)
var alpha{v in V, k in K} >= 0;								#Tiempo de inicio del vuelta v por el vehiculo k
var F{objetivos} >=0;
#----------------------------------------------------------------------------------------------------------------------------------------------------------
#Funcion objetivo
minimize FO1 : F[h]																	;	# para minimizar cada objetivo por separado
#minimize FO2 : sum {i in objetivos} betha[i] * (MV[i] - F[i])/(MV[i] - PV[i])		;	# para minimizar la funciones objetivos normalizadas
minimize FO2 : sum {i in objetivos} betha[i] * (F[i] - MV[i])/(PV[i] - MV[i])       ;
O2: F[1] = sum {i in N, j in N, p in P, v in V, k in K: (i,j) in A}(e[i,j,p]+ee[j,p])*X[i,j,p,v,k] ; #EMISIONES
O3: F[2] = sum {i in N, j in N, p in P, v in V, k in K: (i,j) in A}(g[i,j,p]+gg[j,p])*X[i,j,p,v,k] ; #COSTOS

#----------------------------------------------------------------------------------------------------------------------------------------------------------
#RESTRICCIONES

#RESTRICCIONES DE ORIGEN, DESTINO Y FLUJO
R1{j in N, v in V, k in K: j !=O}: sum{i in N, p in P:(i,j) in A and i!=j}X[i,j,p,v,k] >= Y[j,v,k];   	#los arcos visitados deben ser menor o igual a los clientes vistados
R2{i in N, v in V, k in K: i !=O}: sum{j in N, p in P:(i,j) in A and j!=i}X[i,j,p,v,k] >= Y[i,v,k];		#los arcos visitados deben ser menor o igual a los clientes vistados

R3{i in N: i!=O and i!=20}: sum{j in N, p in P, v in V, k in K:(i,j) in A}X[i,j,p,v,k] = 1;				#se debe ir a cada nodo solo una vez
R4{j in N: j!=O and j!=20}: sum{i in N, p in P, v in V, k in K:(i,j) in A}X[i,j,p,v,k] = 1;				#se debe salir a cada nodo solo una vez 

R5{v in V, k in K}: sum{j in N, p in P:(O,j) in A}X[O,j,p,v,k] <= card{K};								#debe salir del origen a lo mas la cantidad de vueltas del conjunto V  
R6{v in V, k in K}: sum{j in N, p in P:(j,20) in A}X[j,20,p,v,k] <= card{K};							#nueva restriccion que dice que desde algun nodo j debe ir a 8 a los mas la cantidad k de veces
	
R7{v in V:v!=1}: sum{j in N, p in P, k in K:(O,j) in A}X[O,j,p,v,k] >= 1;								#obliga a que se salga desde origen mas de una vez en las vueltas distints a la primera
R8{v in V:v!=1}: sum{j in N, p in P, k in K:(j,20) in A}X[j,20,p,v,k] >= 1;								#para las vueltas distintas a la primera, permite ir desde algun j hacia el nodo 20 de una vez	
R9{j in N: j!=20}: sum{v in V, k in K}Y[j,v,k] = 1;													#todos los clientes deben ser visitados

#RESTRICCIONES DE SECUENCIALIDAD
R10: sum{j in N, p in P:(O,j) in A}X[O,j,p,1,1] = 1;													#obliga a que se salga desde el origen con el camion 1 en la vuelta 1
R11{k in K}: sum{j in N, p in P:(j,20) in A }X[j,20,p,1,k] >= 1;								#obliga a volver al origen 
	
#R13{k in K:k<card{K}}: sum{j in N, p in P, v in V:(O,j) in A}X[O,j,p,v,k] >= sum{j in N, p in P, v in V:(j,20) in A}X[j,20,p,v,k+1];	#Restringe que debe salir con el siguiente camion una vez que ya salio el anterior RESTRICCION PARASITA, NO SE ACERCA A LA REALIDAD
R14{k in K, p in P, v in V:v<=card{V}-1}: sum{i in N, j in N:(i,j) in A}X[i,j,p,v+1,k] <= sum{i in N, j in N:(i,j) in A}X[i,j,p,v,k];	#Secuencia de vueltas

#RESTRICCION DE CAPACIDAD
R15{v in V, k in K}: sum{i in N}Y[i,v,k]*d[i] <= q;			#restriccion de capacidad
R16{v in V, k in K, j in N: j!=O and j != 20}: sum{p in P} X[20,j,p,v,k] = 0;  #Desde el nodo ficticio no puede ir a ningÃºn otro nodo que no sea el origen, debe volver al origen para que parta desde el en las siguientes vueltas

#Restricciones de tiempo
#R17{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j and i!=20}: t[i,v,k] <= LS[p] + B2*(1 - X[i,j,p,v,k]);	#limite superior
#R18{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j and p>=1 and i!=20}: t[i,v,k] >= LI[p]- B2*(1 - X[i,j,p,v,k]);	

R177{i in N, v in V, k in K: i!=20}: t[i,v,k] <= sum{p in P, j in N: (i,j) in A and j!= O and i!=j} LS[p] * X[i,j,p,v,k]; #limite superior
R188{i in N, v in V, k in K: i!=20}: t[i,v,k] >= sum{p in P, j in N: (i,j) in A and j!= O and i!=j and p>1} LI[p] * X[i,j,p,v,k]; #limite inferior	

R19{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j}: t[j,v,k] >= t[i,v,k] + (T[i,j,p] + tt[j,p]) - (1 - X[i,j,p,v,k])*B1;	#Restriccion que calcula el tiempo de salida de cada nodo
R20{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j}: t[j,v,k] <= t[i,v,k] + (T[i,j,p] + tt[j,p]) + (1 - X[i,j,p,v,k])*B1;	#tiempo maximo en que puede circular por el arco debe ser menor al tiempo o intervao temporal entre (i,j)
#R19{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j}: t[j,v,k] >= t[i,v,k] + (T[i,j,p] + tt[j,p])  - (1 - X[i,j,p,v,k])*B1;	#Restriccion que calcula el tiempo de salida de cada nodo
#R20{i in N, j in N, p in P, v in V, k in K:(i,j) in A and j!=O and i!=j}: t[j,v,k] <= t[i,v,k] + (T[i,j,p]+ tt[j,p]) - (X[i,j,p,v,k] - 1)*B1;

#R222{v in V, k in K} : alpha[v,k]=	0;
#.RUN
R21{k in K}: t[O,1,k] = TDP + alpha[1,k];	#restriccion que muestra entre el inicio real y programado
R22{i in N, v in V, k in K: v!=1}: t[O,v,k] = t[20,v-1,k] + alpha[v,k];	#restriccion que muestra entre el inicio real y programado

#Eliminacion de subtours
/*r23{i in N, j in N, v in V, k in K: (i,j) in A and j!=20}: sum{p in P}X[i,j,p,v,k] + sum{p in P}X[j,i,p,v,k] <= 1; 	
r24{i in N, j in N, k2 in N, v in V, k in K: (i,j) in A and (j,k2) in A and i != k2}: sum{p in P}X[i,j,p,v,k] + sum{p in P}X[j,k2,p,v,k] + sum{p in P}X[k2,i,p,v,k] <= 2; 	
r25{i in N, j in N, k2 in N, l in N, v in V, k in K: (i,j) in A and (j,k2) in A and (k2,l) in A and i != k2 and i != l and j!=l}: sum{p in P}X[i,j,p,v,k] +sum{p in P} X[j,k2,p,v,k] + sum{p in P}X[k2,l,p,v,k] + sum{p in P}X[l,i,p,v,k] <= 3; 	
r26{i in N, j in N, k2 in N, l in N, m2 in N, v in V, k in K: (i,j) in A and (j,k2) in A and (k2,l) in A and (l,m2) in A and i != k2 and i != l and j!=l and i!= m2 and j!=m2 and k2!=m2}: sum{p in P}X[i,j,p,v,k] +sum{p in P} X[j,k2,p,v,k] + sum{p in P}X[k2,l,p,v,k] + sum{p in P}X[l,m2,p,v,k] + sum{p in P}X[m2,i,p,v,k]<= 4; 	
*/
#Eliminacion de subtours
r23{v in V, k in K, (i,j) in A,(j,k2) in A : i = k2}: sum{p in P} (X[i,j,p,v,k] +  X[j,k2,p,v,k]) <= 1; 	
r24{v in V, k in K, (i,j) in A,(j,k2) in A, (k2, l) in A: i = l}: sum{p in P} (X[i,j,p,v,k] + X[j,k2,p,v,k] + X[k2,l,p,v,k]) <= 2; 	
r25{v in V, k in K, (i,j) in A,(j,k2) in A, (k2, l) in A, (l, m2) in A: i = m2}: sum{p in P} (X[i,j,p,v,k] + X[j,k2,p,v,k] + X[k2,l,p,v,k] + X[l,m2,p,v,k]) <= 3; 	
r26{v in V, k in K, (i,j) in A,(j,k2) in A, (k2, l) in A, (l, m2) in A, (m2, n2) in A: i = n2}: sum{p in P}(X[i,j,p,v,k] + X[j,k2,p,v,k] + X[k2,l,p,v,k] + X[l,m2,p,v,k] + X[m2,n2,p,v,k])<= 4; 	

