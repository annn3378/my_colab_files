## Задача тактического планирования Glass pro

# Множества

set PLANTS; # множество заводов
set CLIENTS; # множество клиентов
set PRODUCTS; # множество товаров

# Параметры

#путь к файлу источника данных
param conn symbolic := 'FILEDSN=.\glasspro.dsn' ;

#Загрузка скалярных параметров
set PARAMETERS; #вспомогательное множество - параметров
param parameter_value{PARAMETERS}; #вспомогательный параметр - значения параметров

table params IN 'ODBC' conn
	'params' :
	PARAMETERS <- [parameter_name], parameter_value;

param T := parameter_value['T']; #максимальный номер временного периода (из базы)
param truck_capacity := parameter_value['truck_capacity']; #бутылок в грузовике (из базы)
param pallet_capacity := parameter_value['pallet_capacity']; #бутылок на паллете (из базы)


param capacity {PLANTS, 1..T}; # производственные мощности в бутылках
param space {PLANTS}; # доступные площади для хранения в паллетах

param make_cost {PLANTS, PRODUCTS}; # себестоимость производства одной бутылки
param store_cost {PLANTS}; # стоимость хранения одной паллеты на заводе
param inv0 {PLANTS, PRODUCTS} >= 0 default 0; # начальный уровень запасов

param demand {CLIENTS, PRODUCTS, 1..T} >= 0 default 0; # спрос клиента на продукт в бутылках
param tariff {PLANTS, CLIENTS, 1..T}; # транспортный тариф на маршрут

/** нужно добавить штраф по умолчанию, который используется,
 если не указан спрос: 0 */
param shortage_penalty {CLIENTS, PRODUCTS, 1..T} default 0; # штраф за недопоставку 



/** убрали значения параметров, будут считываться из базы!
param T > 0; # множество временных периодов
param truck_capacity > 0; # вместимость одной фуры (в бутылках)
param pallet_capacity > 0; # вместимость одной паллеты (в бутылках)
*/

/* Загрузка данных из базы */

#Загрузка списка продуктов
table t_products IN 'ODBC' conn
	'products' :
	PRODUCTS <- [id];

#Загрузка списка клиентов
table t_clients IN 'ODBC' conn
	'clients' :
	CLIENTS <- [id];
	
#Загрузка списка заводов и их свойств
table t_plants IN 'ODBC' conn
	'plants' :
	PLANTS <- [id], space, store_cost ;

#Прогноз спроса
table t_demand IN 'ODBC' conn
	'demand' :
	[client, product, period], demand, shortage_penalty;

#Транспортные тарифы
table t_rates IN 'ODBC' conn
	'rates' :
	[plant, client, period], tariff;
	
#Себестоимость производства
table t_production_cost IN 'ODBC' conn
	'plant_products' :
	[plant, product], make_cost, inv0;

#Мощности
table t_capacity IN 'ODBC' conn
	'capacity' :
	[plant, period], capacity;


# Переменные 

var make {PLANTS, PRODUCTS, 1..T} >= 0; # объем производства в бутылках
var store {PLANTS, PRODUCTS, 0..T} >= 0; # уровень запасов в бутылках
var ship {PLANTS, CLIENTS, PRODUCTS, 1..T} >= 0; # объем отгрузок в бутылках

var tship {PLANTS, CLIENTS, 1..T} >= 0; # общий объем отгрузок с завода клиенту за период (см. "Вспомогательные ограничения") 
var ntrucks {PLANTS, CLIENTS, 1..T} >= 0 integer; # количество фур на маршруте (см. "Вспомогательные ограничения")
var npallets {PLANTS, PRODUCTS, 1..T} >= 0; # количество паллет на хранении (см. "Вспомогательные ограничения")

# Переменные для записи целевой функции

var Total_Production_Costs >= 0; # Общие производственные затраты
var Total_Storage_Costs >= 0; # Общие затраты на хранение продукции
var Total_Transport_Costs >= 0; # Общие транспортные затраты
var Total_Penalties >= 0; # Сумма штрафов за недопоставки

# Раздельный расчет компонентов целевой функции с помощью ограничений

subject to ProductionCosts:
	Total_Production_Costs = sum {p in PLANTS, i in PRODUCTS, t in 1..T} make [p,i,t] * make_cost[p,i];

subject to StorageCosts:
	Total_Storage_Costs = sum {p in PLANTS, i in PRODUCTS, t in 1..T} npallets[p,i,t] * store_cost[p];

subject to TransportCosts:
	Total_Transport_Costs = sum {p in PLANTS, c in CLIENTS, t in 1..T} ntrucks[p,c,t] * tariff[p,c,t];

subject to ShortagePenalties:
	Total_Penalties = sum {c in CLIENTS, i in PRODUCTS, t in 1..T} ((demand[c,i,t] - sum {p in PLANTS} ship[p,c,i,t])*shortage_penalty[c,i,t]);

# Целевая функция

minimize TotalCosts:
	Total_Production_Costs + Total_Storage_Costs + Total_Transport_Costs + Total_Penalties;

# Вспомогательные ограничения

subject to ShipmentPerPeriod {p in PLANTS, c in CLIENTS, t in 1..T}: tship[p,c,t] = sum {i in PRODUCTS} ship[p,c,i,t]; # общий объем отгрузок с завода клиенту за период

subject to NumberOfTrucks {p in PLANTS, c in CLIENTS, t in 1..T}: ntrucks[p,c,t] * truck_capacity >= tship[p,c,t]; # количество фур на маршруте

subject to NumberOfPallets {p in PLANTS, i in PRODUCTS, t in 1..T}: npallets[p,i,t] = (store[p,i,t] / pallet_capacity); # количество паллет на хранении

# Ограничения

subject to CapacityLimit {p in PLANTS, t in 1..T}:
	sum {i in PRODUCTS} make[p,i,t] <= capacity[p,t]; # ограничение на производственные мощности; предполагается производство всех видов продукции на одних и тех же мощностях

subject to SpaceLimit {p in PLANTS, t in 1..T}:
	sum {i in PRODUCTS} npallets[p,i,t] <= space[p]; # ограничение на доступные складские площади на заводе; продукция хранится на одних и тех же площадях

subject to InitialInventory {p in PLANTS, i in PRODUCTS}:
	inv0[p,i] = store[p,i,0]; # первоначальный запас

subject to Balance {p in PLANTS, i in PRODUCTS, t in 1..T}:
	sum {c in CLIENTS} (ship[p,c,i,t]) + store[p,i,t] = make[p,i,t] + store[p,i,t-1]; # уравнение баланса

subject to ClientDemand {c in CLIENTS, i in PRODUCTS, t in 1..T}:
	sum {p in PLANTS} ship[p,c,i,t] <= demand[c,i,t]; # обязательство по удовлетворению спроса


/*Вспомогательные переменные и ограничения для вывода результатов */

var service {t in 1..T} >= 0;
subject to Service_T {t in 1..T} :
	service[t] =
		(sum {p in PLANTS, c in CLIENTS, i in PRODUCTS} ship[p, c, i, t]) / 
			(sum {c in CLIENTS, i in PRODUCTS} demand[c, i, t]) * 100;

var production_cost {t in 1..T} >= 0;
subject to Production_Cost_T {t in 1..T} :
	production_cost[t] = 
		sum {p in PLANTS, i in PRODUCTS} 
			make [p,i,t] * make_cost[p,i];

var storage_cost {t in 1..T} >= 0;
subject to Storage_Cost_T {t in 1..T} :
	storage_cost[t] = 
		sum {p in PLANTS, i in PRODUCTS} 
			npallets [p,i,t] * store_cost[p];

var shipping_cost {t in 1..T} >= 0;
subject to Shipping_Cost_T {t in 1..T} :
	shipping_cost[t] = 
		sum {p in PLANTS, c in CLIENTS} 
			ntrucks[p,c,t] * tariff[p,c,t];

var penalties {t in 1..T} >= 0;
subject to Penalties {t in 1..T} :
	penalties[t] = 
		sum {c in CLIENTS, i in PRODUCTS} 
		((demand[c,i,t] 
			- sum {p in PLANTS} ship[p,c,i,t])*shortage_penalty[c,i,t]);
			
solve;
display TotalCosts;
/*
printf '\n\n';
printf 'Объемы производства:\n\n';
printf '%-10s', 'Завод';
printf '%12s', 'Тип бутылки';
printf '%12s', 'Период';
printf '%16s', 'Объем выпуска';
printf '\n';
for {p in PLANTS, i in PRODUCTS, t in 1..T} {
printf '%-10s', p;
printf '%12s', i;
printf '%12s', t;
printf '%16.0f\n', make[p,i,t];}
*/


/* Сохранение результатов в базу данных */

# План производства и уровни запасов 
table rpt_production {p in PLANTS, i in PRODUCTS, t in 1..T} OUT 'ODBC' conn
	'DELETE FROM rpt_production;'
	'rpt_production' :
	p ~ plant, i ~ product, t ~ period, make[p, i, t] ~ make, 
	store[p, i, t] ~ store, capacity[p, t] ~ capacity_available,
	make[p, i, t] / capacity[p, t]  * 100 ~ capacity_utilization,
	space[p] ~ space_available, npallets[p, i, t] ~ space_used,
	npallets[p, i, t] / space[p] * 100 ~ space_utilization,
	sum {c in CLIENTS} ship[p, c, i, t] ~ship;

# Использование складов
table rpt_stock {p in PLANTS, t in 1..T} OUT 'ODBC' conn
	'DELETE FROM rpt_stock;'
	'rpt_stock' :
	p ~ plant, t ~ period, 
	sum {i in PRODUCTS} npallets[p, i, t] ~ space_used,
	space[p] ~ space_available,
	100 * sum {i in PRODUCTS} npallets[p, i, t] / space[p] ~ space_utilization;


# Целевые показатели

table rpt_objectives {t in 1..T} OUT 'ODBC' conn
	'DELETE FROM rpt_objectives;'
	'rpt_objectives' :
	t ~ period, 
	service[t] ~ service,
	production_cost[t] ~ production_cost,
	storage_cost[t]~ storage_cost,
	shipping_cost[t]~ shipping_cost,
	penalties[t] ~ penalties;
	

# Уровень сервиса
table rpt_service {c in CLIENTS, i in PRODUCTS, t in 1..T : demand[c,i,t] > 0}
	OUT 'ODBC' conn
	'DELETE FROM rpt_service;'
	'rpt_service' :
	c ~ client, i ~ product, t ~ period,
	demand[c, i, t] ~ demand,
	sum {p in PLANTS} ship[p, c, i, t] ~ ship,
	(demand[c, i, t] 
		- sum {p in PLANTS} ship[p, c, i, t]) 
			* shortage_penalty[c, i, t] ~shortage_penalty,
	(sum {p in PLANTS} ship[p, c, i, t]) / demand[c, i, t] * 100 ~service;


# Перевозки
#по отдельным товарам
table rpt_shipping {p in PLANTS, c in CLIENTS, i in PRODUCTS, t in 1..T : 
	ship[p, c,i,t] > 0}
	OUT 'ODBC' conn
	'DELETE FROM rpt_shipping;'
	'rpt_shipping' :
	p~ plant, c ~ client, i ~ product, t ~ period,
	ship[p, c, i, t] ~ ship;

#число грузовиков по направлению и коэффициент использования
table rpt_trucks {p in PLANTS, c in CLIENTS, t in 1..T : ntrucks[p, c, t] > 0}
	OUT 'ODBC' conn
	'DELETE FROM rpt_trucks;'
	'rpt_trucks' :
	p~ plant, c ~ client, t ~ period, ntrucks[p, c, t] ~ ntrucks,
	100 * (sum{i in PRODUCTS} ship[p, c, i, t]) / (ntrucks[p, c, t] * truck_capacity) ~ utilization;


end;
